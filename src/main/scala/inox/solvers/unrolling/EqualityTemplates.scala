/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.immutable.VectorMap
import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

/** Incrementally unfolds equality relations between types for which the
  * SMT notion of equality is not relevant.
  *
  * @see [[ast.Definitions.ADTSort.equality]] for such a case of equality
  */
trait EqualityTemplates { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import equalityManager._

  /** The caches of the equality templates, which push and pop leave as they are. Each one maps its
    * key to a value that only depends on the key and the program, or to a fresh symbol that stands
    * for the same thing wherever it is used (see [[functionCaches]]).
    *
    * The equality symbols are among them: the cached templates, of equalities and of functions,
    * mention the symbols of the types they compare, so a pop can't give a type a new one. */
  private object equalityCaches {
    /** Whether the equality of each type is unrolled (see [[unrollEquality]]), and the sorts whose
      * equality is being decided. */
    val unroll: MutableMap[Type, Boolean] = MutableMap.empty
    val checking: MutableSet[TypedADTSort] = MutableSet.empty
    /** The equality symbol of each type (see [[equalitySymbol]]). */
    val symbols: MutableMap[Type, (Variable, Encoded)] = MutableMap.empty
    /** The template of the equality of each type (see [[EqualityTemplate]]). */
    val templates: MutableMap[Type, EqualityTemplate] = MutableMap.empty
    /** The negation of each blocker of equalities (see [[equalityManager.satisfactionAssumptions]]). */
    val negations: MutableMap[Encoded, Encoded] = MutableMap.empty
  }

  def unrollEquality(tpe: Type): Boolean = equalityCaches.unroll.getOrElse(tpe, {
    val res = tpe match {
      case adt: ADTType =>
        val sort = adt.getSort
        sort.hasEquality || (!equalityCaches.checking(sort) && {
          equalityCaches.checking += sort
          sort.constructors.exists(c => c.fields.exists(vd => unrollEquality(vd.getType)))
        })

      case BooleanType() | UnitType() | CharType() | IntegerType() |
           RealType() | StringType() | (_: BVType) | (_: TypeParameter) => false

      // Functions are compared through their identifiers, and the equality clauses between
      // lambdas compare their closures with `registeredEquality` (see [[LambdaTemplates]]).
      case (_: FunctionType) | (_: PiType) => false

      case NAryType(tpes, _) => tpes.exists(unrollEquality)
    }

    equalityCaches.unroll(tpe) = res
    res
  })

  private lazy val hasCustomEqualities: Boolean = sorts.values.exists(_.flags.exists {
    case HasADTEquality(_) => true
    case _ => false
  })

  /** Whether `tpe` contains a set, bag or map whose elements (or keys) require equality unrolling.
    *
    * The solvers compare these elements structurally (e.g. membership in an SMT set), which
    * disagrees with the custom equality. We therefore reject such types instead of producing
    * spurious counterexamples or proofs.
    */
  def unsupportedContainer(tpe: Type): Boolean = hasCustomEqualities && typeOps.exists {
    case SetType(base) => unrollEquality(base)
    case BagType(base) => unrollEquality(base)
    case MapType(from, _) => unrollEquality(from)
    case _ => false
  } (tpe)

  def equalitySymbol(tpe: Type): (Variable, Encoded) = {
    equalityCaches.symbols.getOrElseUpdate(tpe, {
      val v = Variable.fresh("eq" + tpe, FunctionType(Seq(tpe, tpe), BooleanType()))
      v -> encodeSymbol(v)
    })
  }

  /** The equality of `e1` and `e2` at `tpe`, which is unrolled under `blocker` when `tpe` has an
    * equality symbol (see [[guardedEquality]] for one that isn't). */
  private[unrolling] def registeredEquality(blocker: Encoded, tpe: Type, e1: Encoded, e2: Encoded): Encoded =
    if (unrollEquality(tpe)) registerEquality(blocker, tpe, e1, e2) else mkEquals(e1, e2)

  class EqualityTemplate private(val tpe: Type, val contents: TemplateContents) extends Template {
    override protected def instantiate(instantiation: Instantiation): Clauses = {
      // register equalities (WILL NOT lead to any [[instantiate]] calls)
      instantiation.clauses(onEquality = { (bp, equality) =>
        registerEquality(bp, equality)
        Seq.empty
      })
    }
  }

  object EqualityTemplate {
    def apply(tpe: Type): EqualityTemplate = equalityCaches.templates.getOrElse(tpe, {
      val (f, fT) = equalitySymbol(tpe)
      val args @ Seq(e1, e2) = Seq("e1", "e2").map(s => Variable.fresh(s, tpe))
      val argsT = args.map(encodeSymbol)

      val pathVar = Variable.fresh("b", BooleanType(), true)
      val pathVarT = encodeSymbol(pathVar)

      val tmplClauses = mkClauses0(pathVar, Equals(Application(f, args), tpe match {
        case adt: ADTType =>
          val sort = adt.getSort

          if (sort.hasEquality) {
            sort.equality.get.applied(args)
          } else {
            orJoin(sort.constructors.map { tcons =>
              val instCond = and(isCons(e1, tcons.id), isCons(e2, tcons.id))
              val fieldConds = tcons.fields.map(vd => Equals(ADTSelector(e1, vd.id), ADTSelector(e2, vd.id)))
              andJoin(instCond +: fieldConds)
            })
          }

        case TupleType(tps) =>
          andJoin(tps.indices.map(i => Equals(TupleSelect(e1, i + 1), TupleSelect(e2, i + 1))))

        case (_: SetType) | (_: BagType) | (_: MapType) =>
          throw new Unsupported(s"Equality on ${tpe.asString} relies on a custom equality inside a set, bag or map")

        case _ => throw new InternalSolverError(s"Why does $tpe require equality unrolling!?")
      }), (args zip argsT).toMap + (f -> fT) + (pathVar -> pathVarT))

      val (contents, _) = Template.contents(
        pathVar -> pathVarT, args zip argsT, tmplClauses,
        substMap = Map(f -> fT), optApp = Some(fT -> FunctionType(Seq(tpe, tpe), BooleanType()))
      )

      val res = new EqualityTemplate(tpe, contents)
      equalityCaches.templates(tpe) = res
      res
    })
  }

  /** Whether an equality was instantiated, i.e. whether equality symbols can hold on distinct
    * terms (see [[delayedPurityClauses]]).
    */
  def equalitiesInstantiated: Boolean = state.get.eqBlockers.nonEmpty

  def instantiateEquality(blocker: Encoded, equality: Equality): Clauses = {
    val Equality(tpe, e1, e2) = equality
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]

    def instantiated: Set[(Encoded, Encoded, Encoded)] = state.get.instantiated.getOrElse(tpe, Set.empty)
    def addInstantiated(is: (Encoded, Encoded, Encoded)*): Unit =
      state.update(s => s.copy(instantiated = s.instantiated.updated(tpe, s.instantiated.getOrElse(tpe, Set.empty) ++ is)))

    if (!instantiated((blocker, e1, e2))) {
      val eqBlocker = state.get.eqBlockers.get(equality) match {
        case Some(eqBlocker) =>
          eqBlocker

        case None =>
          if (!equalitiesInstantiated) clauses ++= delayedPurityClauses

          val eqBlocker = encodeSymbol(Variable.fresh("q", BooleanType(), true))
          state.update(s => s.copy(eqBlockers = s.eqBlockers.updated(equality, eqBlocker)))

          clauses ++= Rule.Unfold(EqualityTemplate(tpe), eqBlocker, Seq(Left(e1), Left(e2)), None).clauses

          // the equalities instantiated so far that chain with this one
          for ((tb, te1, te2) <- instantiated; cond = mkAnd(eqBlocker, tb)) {
            if (e2 == te1) {
              clauses ++= Rule.Transitivity(tpe, cond, e1, e2, te2).clauses
              addInstantiated((cond, e1, te2))
            }

            if (te2 == e1) {
              clauses ++= Rule.Transitivity(tpe, cond, te1, te2, e2).clauses
              addInstantiated((cond, te1, e2))
            }
          }

          clauses ++= Rule.Symmetry(tpe, eqBlocker, e1, e2).clauses
          addInstantiated((eqBlocker, e1, e2), (eqBlocker, e2, e1))

          clauses ++= Rule.Reflexivity(tpe, e1, e2, None).clauses
          eqBlocker
      }

      if (eqBlocker != blocker) {
        registerImplication(blocker, eqBlocker)
        clauses ++= Rule.Enables(blocker, eqBlocker).clauses
      }

      reporter.debug("Unrolling equality behind " + equality + " (" + clauses.size + ")")
      for (cl <- clauses) {
        reporter.debug("  . " + cl)
      }
    }

    clauses.toSeq
  }

  def registerEquality(blocker: Encoded, tpe: Type, e1: Encoded, e2: Encoded): Encoded = {
    registerEquality(blocker, Equality(tpe, e1, e2))
  }

  def registerEquality(blocker: Encoded, equality: Equality): Encoded = {
    val tpe = equality.tpe
    state.update(s => s.copy(equalities = s.equalities.register(blocker, nextGeneration(currentGeneration), Set(equality))))

    mkApp(equalitySymbol(tpe)._2, FunctionType(Seq(tpe, tpe), BooleanType()), Seq(equality.e1, equality.e2))
  }

  /** The state of [[equalityManager]], which push saves and pop restores as a whole.
    *
    * @param equalities the equalities that each blocker guards, which are unfolded with it
    * @param eqBlockers the blocker of each unfolded equality, under which its template is
    *                   instantiated, in the order in which the equalities were unfolded
    * @param instantiated the pairs of terms of each type whose equality holds under a condition,
    *                     with that condition, which [[Rule.Transitivity]] chains */
  private[unrolling] case class EqualityState(
    equalities: Pending[Encoded, Equality],
    eqBlockers: VectorMap[Equality, Encoded],
    instantiated: Map[Type, Set[(Encoded, Encoded, Encoded)]])

  private[unrolling] object equalityManager extends Manager {
    private[EqualityTemplates] val state = new Snapshots(EqualityState(Pending.empty, VectorMap.empty, Map.empty))

    val incrementals: Seq[IncrementalState] = Seq(state)

    def unrollGeneration: Option[Int] = state.get.equalities.generation

    def satisfactionAssumptions: Seq[Encoded] =
      state.get.equalities.keys.toSeq.map(b => equalityCaches.negations.getOrElseUpdate(b, mkNot(b)))
    def refutationAssumptions: Seq[Encoded] = Seq.empty

    def promoteBlocker(b: Encoded): Boolean = state.get.equalities.promote(b) match {
      case Some(equalities) =>
        state.update(_.copy(equalities = equalities))
        true
      case None =>
        false
    }

    def unroll: Clauses = if (state.get.equalities.isEmpty) Seq.empty else {
      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val (due, rest) = state.get.equalities.dequeue
      state.update(_.copy(equalities = rest))
      for ((blocker, _, eqs) <- due; e <- eqs) {
        newClauses ++= instantiateEquality(blocker, e)
      }

      reporter.debug("Unrolling equalities (" + newClauses.size + ")")
      for (cl <- newClauses) {
        reporter.debug("  . " + cl)
      }

      newClauses.toSeq
    }
  }
}
