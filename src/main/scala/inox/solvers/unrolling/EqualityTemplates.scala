/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

/** Incrementally unfolds equality relations between types for which the
  * SMT notion of equality is not relevant.
  *
  * @see [[ast.Definitions.ADTDefinition.equality]] for such a case of equality
  */
trait EqualityTemplates { self: Templates =>
  import context._
  import program._
  import program.trees._
  import program.symbols._

  import equalityManager._

  private val checking: MutableSet[TypedADTDefinition] = MutableSet.empty
  private val unrollCache: MutableMap[Type, Boolean] = MutableMap.empty

  def unrollEquality(tpe: Type): Boolean = unrollCache.getOrElseUpdate(tpe, tpe match {
    case adt: ADTType =>
      val root = adt.getADT.root
      root.hasEquality || (!checking(root) && {
        checking += root
        val constructors = root match {
          case tsort: TypedADTSort => tsort.constructors
          case tcons: TypedADTConstructor => Seq(tcons)
        }

        constructors.exists(c => c.fieldsTypes.exists(unrollEquality))
      })

    case BooleanType | UnitType | CharType | IntegerType |
         RealType | StringType | (_: BVType) | (_: TypeParameter) => false

    case NAryType(tpes, _) => tpes.exists(unrollEquality)
  })

  def equalitySymbol(tpe: Type): (Variable, Encoded) = {
    val rt = bestRealType(tpe)
    typeSymbols.cached(rt) {
      val v = Variable.fresh("eq" + rt, FunctionType(Seq(rt, rt), BooleanType))
      v -> encodeSymbol(v)
    }
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

      val pathVar = Variable.fresh("b", BooleanType, true)
      val pathVarT = encodeSymbol(pathVar)

      val tmplClauses = mkClauses(pathVar, Equals(Application(f, args), tpe match {
        case adt: ADTType =>
          val root = adt.getADT.root

          if (root.hasEquality) {
            root.equality.get.applied(args)
          } else {
            val constructors = root match {
              case tsort: TypedADTSort => tsort.constructors
              case tcons: TypedADTConstructor => Seq(tcons)
            }

            orJoin(constructors.map { tcons =>
              val (instCond, asE1, asE2) = if (tcons == root) (BooleanLiteral(true), e1, e2) else (
                and(IsInstanceOf(e1, tcons.toType), IsInstanceOf(e2, tcons.toType)),
                AsInstanceOf(e1, tcons.toType),
                AsInstanceOf(e2, tcons.toType)
              )

              val fieldConds = tcons.fields.map(vd => Equals(ADTSelector(asE1, vd.id), ADTSelector(asE2, vd.id)))
              andJoin(instCond +: fieldConds)
            })
          }

        case TupleType(tps) =>
          andJoin(tps.indices.map(i => Equals(TupleSelect(e1, i + 1), TupleSelect(e2, i + 1))))

        case _ => throw FatalError(s"Why does $tpe require equality unrolling!?")
      }), (args zip argsT).toMap + (f -> fT) + (pathVar -> encodeSymbol(pathVar)))

      val (contents, _) = Template.contents(
        pathVar -> pathVarT, args zip argsT, tmplClauses,
        substMap = Map(f -> fT), optApp = Some(fT -> FunctionType(Seq(tpe, tpe), BooleanType))
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
      val ft = FunctionType(Seq(tpe, tpe), BooleanType)

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
    registerEquality(blocker, Equality(bestRealType(tpe), e1, e2))
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

    mkApp(equalitySymbol(tpe)._2, FunctionType(Seq(tpe, tpe), BooleanType), Seq(equality.e1, equality.e2))
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
