/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

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

  private val checking: MutableSet[TypedADTSort] = MutableSet.empty
  private val unrollCache: MutableMap[Type, Boolean] = MutableMap.empty

  def unrollEquality(tpe: Type): Boolean = unrollCache.getOrElse(tpe, {
    val res = tpe match {
      case adt: ADTType =>
        val sort = adt.getSort
        sort.hasEquality || (!checking(sort) && {
          checking += sort
          sort.constructors.exists(c => c.fields.exists(vd => unrollEquality(vd.getType)))
        })

      case BooleanType() | UnitType() | CharType() | IntegerType() |
           RealType() | StringType() | (_: BVType) | (_: TypeParameter) => false

      // Functions are compared through their identifiers, and the equality clauses between
      // lambdas compare their closures with `mkEqualities` (see [[LambdaTemplates]]).
      case (_: FunctionType) | (_: PiType) => false

      case NAryType(tpes, _) => tpes.exists(unrollEquality)
    }

    unrollCache(tpe) = res
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
    typeSymbols.cached(tpe) {
      val v = Variable.fresh("eq" + tpe, FunctionType(Seq(tpe, tpe), BooleanType()))
      v -> encodeSymbol(v)
    }
  }

  private[unrolling] def mkEqualities(
    blocker: Encoded,
    tpe: Type,
    e1: Encoded,
    e2: Encoded,
    register: Boolean = true
  ): (Encoded, Clauses) = {
    if (register && unrollEquality(tpe)) (registerEquality(blocker, tpe, e1, e2), Seq())
    else guardedEquality(blocker, tpe, e1, e2)
  }

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
    private val cache: MutableMap[Type, EqualityTemplate] = MutableMap.empty

    def apply(tpe: Type): EqualityTemplate = cache.getOrElse(tpe, {
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
      cache(tpe) = res
      res
    })
  }

  /** Whether an equality was instantiated, i.e. whether equality symbols can hold on distinct
    * terms (see [[delayedPurityClauses]]).
    */
  def equalitiesInstantiated: Boolean = eqBlockers.nonEmpty

  def instantiateEquality(blocker: Encoded, equality: Equality): Clauses = {
    val Equality(tpe, e1, e2) = equality
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]

    if (!instantiated(tpe)((blocker, e1, e2))) {
      val eqBlocker = eqBlockers.get(equality) match {
        case Some(eqBlocker) =>
          eqBlocker

        case None =>
          if (!equalitiesInstantiated) clauses ++= delayedPurityClauses

          val eqBlocker = encodeSymbol(Variable.fresh("q", BooleanType(), true))
          eqBlockers += equality -> eqBlocker

          clauses ++= Rule.Unfold(EqualityTemplate(tpe), eqBlocker, Seq(Left(e1), Left(e2)), None).clauses

          // the equalities instantiated so far that chain with this one
          for ((tb, te1, te2) <- instantiated(tpe); cond = mkAnd(eqBlocker, tb)) {
            if (e2 == te1) {
              clauses ++= Rule.Transitivity(tpe, cond, e1, e2, te2).clauses
              instantiated += tpe -> (instantiated(tpe) + ((cond, e1, te2)))
            }

            if (te2 == e1) {
              clauses ++= Rule.Transitivity(tpe, cond, te1, te2, e2).clauses
              instantiated += tpe -> (instantiated(tpe) + ((cond, te1, e2)))
            }
          }

          clauses ++= Rule.Symmetry(tpe, eqBlocker, e1, e2).clauses
          instantiated += tpe -> (instantiated(tpe) + ((eqBlocker, e1, e2)) + ((eqBlocker, e2, e1)))

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
    equalityInfos.register(blocker, nextGeneration(currentGeneration), Set(equality))

    mkApp(equalitySymbol(tpe)._2, FunctionType(Seq(tpe, tpe), BooleanType()), Seq(equality.e1, equality.e2))
  }

  private[unrolling] object equalityManager extends Manager {
    private[EqualityTemplates] val eqBlockers = new IncrementalMap[Equality, Encoded]()
    private[EqualityTemplates] val typeSymbols = new IncrementalMap[Type, (Variable, Encoded)]
    private[EqualityTemplates] val equalityInfos = new BlockerQueue[Equality]
    private[EqualityTemplates] val instantiated = new IncrementalMap[Type, Set[(Encoded, Encoded, Encoded)]].withDefaultValue(Set.empty)

    val incrementals: Seq[IncrementalState] = Seq(eqBlockers, typeSymbols, equalityInfos, instantiated)

    def unrollGeneration: Option[Int] = equalityInfos.generation

    def satisfactionAssumptions: Seq[Encoded] = equalityInfos.satisfactionAssumptions
    def refutationAssumptions: Seq[Encoded] = Seq.empty

    def promoteBlocker(b: Encoded): Boolean = equalityInfos.promote(b)

    def unroll: Clauses = if (equalityInfos.isEmpty) Seq.empty else {
      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      for ((blocker, _, eqs) <- equalityInfos.dequeue(); e <- eqs) {
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
