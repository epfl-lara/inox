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
  import context._
  import program._
  import program.trees._
  import program.symbols._

  import equalityManager._

  private val checking: MutableSet[TypedADTSort] = MutableSet.empty
  private val unrollCache: MutableMap[Type, Boolean] = MutableMap.empty

  def unrollEquality(tpe: Type): Boolean = unrollCache.getOrElseUpdate(tpe, tpe match {
    case adt: ADTType =>
      val sort = adt.getSort
      sort.hasEquality || (!checking(sort) && {
        checking += sort
        sort.constructors.exists(c => c.fieldsTypes.exists(unrollEquality))
      })

    case BooleanType() | UnitType() | CharType() | IntegerType() |
         RealType() | StringType() | (_: BVType) | (_: TypeParameter) => false

    case NAryType(tpes, _) => tpes.exists(unrollEquality)
  })

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
  ): Encoded = {
    if (!unrollEquality(tpe)) mkEquals(e1, e2)
    else if (register) registerEquality(blocker, tpe, e1, e2)
    else mkApp(equalitySymbol(tpe)._2, FunctionType(Seq(tpe, tpe), BooleanType()), Seq(e1, e2))
  }

  class EqualityTemplate private(val tpe: Type, val contents: TemplateContents) extends Template {
    def instantiate(aVar: Encoded, e1: Encoded, e2: Encoded): Clauses = {
      instantiate(aVar, Seq(Left(e1), Left(e2)))
    }

    override protected def instantiate(substMap: Map[Encoded, Arg]): Clauses = {
      val clauses = Template.instantiate(
        contents.clauses, contents.blockers, contents.applications, contents.matchers,
        Map.empty, substMap)

      // register equalities (WILL NOT lead to any [[instantiate]] calls)
      val substituter = mkSubstituter(substMap.mapValues(_.encoded))
      for ((b, eqs) <- contents.equalities; bp = substituter(b); equality <- eqs) {
        registerEquality(bp, equality.substitute(substituter))
      }

      clauses
    }
  }

  object EqualityTemplate {
    private val cache: MutableMap[Type, EqualityTemplate] = MutableMap.empty

    def apply(tpe: Type): EqualityTemplate = cache.getOrElseUpdate(tpe, {
      val (f, fT) = equalitySymbol(tpe)
      val args @ Seq(e1, e2) = Seq("e1", "e2").map(s => Variable.fresh(s, tpe))
      val argsT = args.map(encodeSymbol)

      val pathVar = Variable.fresh("b", BooleanType(), true)
      val pathVarT = encodeSymbol(pathVar)

      val tmplClauses = mkClauses(pathVar, Equals(Application(f, args), tpe match {
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

        case _ => throw FatalError(s"Why does $tpe require equality unrolling!?")
      }), (args zip argsT).toMap + (f -> fT) + (pathVar -> encodeSymbol(pathVar)))

      val (contents, _) = Template.contents(
        pathVar -> pathVarT, args zip argsT, tmplClauses,
        substMap = Map(f -> fT), optApp = Some(fT -> FunctionType(Seq(tpe, tpe), BooleanType()))
      )

      new EqualityTemplate(tpe, contents)
    })
  }

  def instantiateEquality(blocker: Encoded, equality: Equality): Clauses = {
    val Equality(tpe, e1, e2) = equality
    if (instantiated(tpe)((blocker, e1, e2))) Seq.empty else {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      clauses ++= EqualityTemplate(tpe).instantiate(blocker, e1, e2)

      val (_, f) = equalitySymbol(tpe)
      val ft = FunctionType(Seq(tpe, tpe), BooleanType())

      // congruence is transitive
      for ((tb, te1, te2) <- instantiated(tpe); cond = mkAnd(blocker, tb)) {
        if (e2 == te1) {
          clauses += mkImplies(
            mkAnd(cond, mkApp(f, ft, Seq(e1, e2)), mkApp(f, ft, Seq(e2, te2))),
            mkApp(f, ft, Seq(e1, te2))
          )

          instantiated += tpe -> (instantiated(tpe) + ((cond, e1, te2)))
        }

        if (te2 == e1) {
          clauses += mkImplies(
            mkAnd(cond, mkApp(f, ft, Seq(te1, te2)), mkApp(f, ft, Seq(te2, e2))),
            mkApp(f, ft, Seq(te1, e2))
          )

          instantiated += tpe -> (instantiated(tpe) + ((cond, te1, e2)))
        }
      }

      // congruence is commutative
      clauses += mkImplies(blocker, mkEquals(mkApp(f, ft, Seq(e1, e2)), mkApp(f, ft, Seq(e2, e1))))
      instantiated += tpe -> (instantiated(tpe) + ((blocker, e1, e2)) + ((blocker, e2, e1)))

      clauses += mkImplies(mkEquals(e1, e2), mkApp(f, ft, Seq(e1, e2)))

      clauses.toSeq
    }
  }

  def registerEquality(blocker: Encoded, tpe: Type, e1: Encoded, e2: Encoded): Encoded = {
    registerEquality(blocker, Equality(tpe, e1, e2))
  }

  def registerEquality(blocker: Encoded, equality: Equality): Encoded = {
    val tpe = equality.tpe
    val gen = nextGeneration(currentGeneration)
    val notBlocker = mkNot(blocker)

    equalityInfos.get(blocker) match {
      case Some((exGen, origGen, _, exEqs)) =>
        val minGen = gen min exGen
        equalityInfos += blocker -> (minGen, origGen, notBlocker, exEqs + equality)
      case None =>
        equalityInfos += blocker -> (gen, gen, notBlocker, Set(equality))
    }

    mkApp(equalitySymbol(tpe)._2, FunctionType(Seq(tpe, tpe), BooleanType()), Seq(equality.e1, equality.e2))
  }

  private[unrolling] object equalityManager extends Manager {
    private[EqualityTemplates] val typeSymbols = new IncrementalMap[Type, (Variable, Encoded)]
    private[EqualityTemplates] val equalityInfos = new IncrementalMap[Encoded, (Int, Int, Encoded, Set[Equality])]
    private[EqualityTemplates] val instantiated = new IncrementalMap[Type, Set[(Encoded, Encoded, Encoded)]].withDefaultValue(Set.empty)

    val incrementals: Seq[IncrementalState] = Seq(typeSymbols, equalityInfos, instantiated)

    def unrollGeneration: Option[Int] =
      if (equalityInfos.isEmpty) None
      else Some(equalityInfos.values.map(_._1).min)

    def satisfactionAssumptions: Seq[Encoded] = equalityInfos.map(_._2._3).toSeq
    def refutationAssumptions: Seq[Encoded] = Seq.empty

    def promoteBlocker(b: Encoded): Boolean = {
      if (equalityInfos contains b) {
        val (_, origGen, notB, eqs) = equalityInfos(b)
        equalityInfos += b -> (currentGeneration, origGen, notB, eqs)
        true
      } else {
        false
      }
    }

    def unroll: Clauses = if (equalityInfos.isEmpty) Seq.empty else {
      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val eqBlockers = equalityInfos.filter(_._2._1 <= currentGeneration).toSeq.map(_._1)
      val newEqInfos = eqBlockers.flatMap(id => equalityInfos.get(id).map(id -> _))
      equalityInfos --= eqBlockers

      for ((blocker, (gen, _, _, eqs)) <- newEqInfos; e <- eqs) {
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
