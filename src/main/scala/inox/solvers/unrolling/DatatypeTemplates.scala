/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait DatatypeTemplates { self: Templates =>
  import program._
  import program.trees._
  import program.symbols._

  import datatypesManager._

  type Functions = Set[(Encoded, FunctionType, Encoded)]

  /** Represents a type unfolding of a free variable (or input) in the unfolding procedure */
  case class TemplateTypeInfo(tsort: TypedADTSort, arg: Encoded) {
    override def toString = tsort.toType.asString + "(" + asString(arg) + ")"
  }

  private val cache: MutableMap[Type, DatatypeTemplate] = MutableMap.empty
  private def mkTemplate(tpe: Type): DatatypeTemplate = cache.getOrElseUpdate(tpe, DatatypeTemplate(tpe))

  def registerSymbol(start: Encoded, sym: Encoded, tpe: Type): Clauses = {
    mkTemplate(tpe).instantiate(start, sym)
  }

  private val requireChecking: MutableSet[TypedADTDefinition] = MutableSet.empty
  private val requireCache: MutableMap[Type, Boolean] = MutableMap.empty

  def requiresUnrolling(tpe: Type): Boolean = requireCache.get(tpe) match {
    case Some(res) => res
    case None =>
      val res = tpe match {
        case ft: FunctionType => true

        case adt: ADTType => adt.getADT match {
          case tcons: TypedADTConstructor => tcons.sort.isDefined
          case tadt if requireChecking(tadt.root) => false
          case tadt =>
            requireChecking += tadt.root
            val classTypes = tadt.root +: (tadt.root match {
              case (tsort: TypedADTSort) => tsort.constructors
              case _ => Seq.empty
            })

            classTypes.exists(ct => ct.hasInvariant || (ct match {
              case tcons: TypedADTConstructor => tcons.fieldsTypes.exists(requiresUnrolling)
              case _ => false
            }))
        }

        case BooleanType | UnitType | CharType | IntegerType |
             RealType | StringType | (_: BVType) | (_: TypeParameter) => false

        case NAryType(tpes, _) => tpes.exists(requiresUnrolling)
      }

      requireCache += tpe -> res
      res
  }

  object DatatypeTemplate {

    def apply(tpe: Type): DatatypeTemplate = {
      val v = Variable(FreshIdentifier("x", true), tpe)
      val pathVar = Variable(FreshIdentifier("b", true), BooleanType)

      var condVars = Map[Variable, Encoded]()
      var condTree = Map[Variable, Set[Variable]](pathVar -> Set.empty).withDefaultValue(Set.empty)
      @inline def storeCond(pathVar: Variable, v: Variable): Unit = {
        condVars += v -> encodeSymbol(v)
        condTree += pathVar -> (condTree(pathVar) + v)
      }

      var guardedExprs = Map[Variable, Seq[Expr]]()
      def storeGuarded(pathVar: Variable, expr: Expr): Unit = {
        val prev = guardedExprs.getOrElse(pathVar, Nil)
        guardedExprs += pathVar -> (expr +: prev)
      }

      @inline def iff(e1: Expr, e2: Expr): Unit = storeGuarded(pathVar, Equals(e1, e2))

      var types = Map[Variable, Set[(TypedADTSort, Expr)]]()
      @inline def storeType(pathVar: Variable, tsort: TypedADTSort, arg: Expr): Unit = {
        types += pathVar -> (types.getOrElse(pathVar, Set.empty) + (tsort -> arg))
      }

      var functions = Map[Variable, Set[Expr]]()
      @inline def storeFunction(pathVar: Variable, expr: Expr): Unit = {
        functions += pathVar -> (functions.getOrElse(pathVar, Set.empty) + expr)
      }

      def rec(pathVar: Variable, expr: Expr): Unit = expr.getType match {
        case tpe if !requiresUnrolling(tpe) =>
          // nothing to do here!

        case adt: ADTType =>
          val tadt = adt.getADT

          if (tadt.hasInvariant) {
            storeGuarded(pathVar, tadt.invariant.get.applied(Seq(expr)))
          }

          if (tadt.definition.isSort && tadt.toSort.definition.isInductive) {
            storeType(pathVar, tadt.toSort, expr)
          } else if (tadt != tadt.root) {
            storeGuarded(pathVar, IsInstanceOf(expr, tadt.toType))

            val tpe = tadt.toType
            for (vd <- tadt.toConstructor.fields) {
              rec(pathVar, ADTSelector(AsInstanceOf(expr, tpe), vd.id))
            }
          } else {
            val matchers = tadt.root match {
              case (tsort: TypedADTSort) => tsort.constructors
              case (tcons: TypedADTConstructor) => Seq(tcons)
            }

            for (tcons <- matchers) {
              val tpe = tcons.toType

              if (requiresUnrolling(tpe)) {
                val newBool: Variable = Variable(FreshIdentifier("b", true), BooleanType)
                storeCond(pathVar, newBool)

                for (vd <- tcons.fields) {
                  rec(newBool, ADTSelector(AsInstanceOf(expr, tpe), vd.id))
                }

                val vars = types.keys.toSet ++ functions.keys
                  guardedExprs.flatMap(_._2.flatMap(exprOps.variablesOf))

                if (vars(newBool)) {
                  iff(and(pathVar, IsInstanceOf(expr, tpe)), newBool)
                }
              }
            }
          }

        case TupleType(tpes) =>
          for ((_, idx) <- tpes.zipWithIndex) {
            rec(pathVar, TupleSelect(expr, idx + 1))
          }

        case FunctionType(_, _) =>
          storeFunction(pathVar, expr)

        case _ => scala.sys.error("TODO")
      }

      rec(pathVar, v)

      val (idT, pathVarT) = (encodeSymbol(v), encodeSymbol(pathVar))
      val encoder: Expr => Encoded = mkEncoder(condVars + (v -> idT) + (pathVar -> pathVarT))

      var clauses: Clauses = Seq.empty
      var calls: CallBlockers  = Map.empty

      for ((b, es) <- guardedExprs) {
        var callInfos : Set[Call] = Set.empty

        for (e <- es) {
          callInfos ++= firstOrderCallsOf(e).map { case (id, tps, args) =>
            Call(getFunction(id, tps), args.map(arg => Left(encoder(arg))))
          }

          clauses :+= encoder(Implies(b, e))
        }

        if (callInfos.nonEmpty) calls += encoder(b) -> callInfos
      }

      val encodedTypes: Map[Encoded, Set[TemplateTypeInfo]]  = types.map { case (b, tps) =>
        encoder(b) -> tps.map { case (tacd, expr) => TemplateTypeInfo(tacd, encoder(expr)) }
      }

      val encodedFunctions: Functions = functions.flatMap { case (b, fs) =>
        val bp = encoder(b)
        fs.map(expr => (bp, bestRealType(expr.getType).asInstanceOf[FunctionType], encoder(expr)))
      }.toSet

      new DatatypeTemplate(pathVar -> pathVarT, idT, condVars, condTree,
        clauses, calls, encodedTypes, encodedFunctions)
    }
  }

  class DatatypeTemplate private (
    val pathVar: (Variable, Encoded),
    val argument: Encoded,
    val condVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: CallBlockers,
    val types: Map[Encoded, Set[TemplateTypeInfo]],
    val functions: Functions) extends Template {

    val args = Seq(argument)
    val exprVars = Map.empty[Variable, Encoded]
    val applications = Map.empty[Encoded, Set[App]]
    val lambdas = Seq.empty[LambdaTemplate]
    val matchers = Map.empty[Encoded, Set[Matcher]]
    val quantifications = Seq.empty[QuantificationTemplate]

    def instantiate(blocker: Encoded, arg: Encoded): Clauses = {
      instantiate(blocker, Seq(Left(arg)))
    }

    override def instantiate(substMap: Map[Encoded, Arg]): Clauses = {
      val substituter = mkSubstituter(substMap.mapValues(_.encoded))
      var clauses: Clauses = Seq.empty

      for ((b,tpe,f) <- functions) {
        clauses ++= registerFunction(substituter(b), tpe, substituter(f))
      }

      for ((b, tps) <- types; bp = substituter(b); tp <- tps) {
        val stp = tp.copy(arg = substituter(tp.arg))
        val gen = nextGeneration(currentGeneration)
        val notBp = mkNot(bp)

        typeInfos.get(bp) match {
          case Some((exGen, origGen, _, exTps)) =>
            val minGen = gen min exGen
            typeInfos += bp -> (minGen, origGen, notBp, exTps + stp)
          case None =>
            typeInfos += bp -> (gen, gen, notBp, Set(stp))
        }
      }

      clauses ++ super.instantiate(substMap)
    }
  }

  private[unrolling] object datatypesManager extends Manager {
    val typeInfos = new IncrementalMap[Encoded, (Int, Int, Encoded, Set[TemplateTypeInfo])]

    val incrementals: Seq[IncrementalState] = Seq(typeInfos)

    def unrollGeneration: Option[Int] =
      if (typeInfos.isEmpty) None
      else Some(typeInfos.values.map(_._1).min)

    def satisfactionAssumptions: Seq[Encoded] = typeInfos.map(_._2._3).toSeq
    def refutationAssumptions: Seq[Encoded] = Seq.empty

    def promoteBlocker(b: Encoded): Boolean = {
      if (typeInfos contains b) {
        val (_, origGen, notB, tps) = typeInfos(b)
        typeInfos += b -> (currentGeneration, origGen, notB, tps)
        true
      } else {
        false
      }
    }

    def unroll: Clauses = if (typeInfos.isEmpty) Seq.empty else {
      println("unrolling datatypes")
      val blockers = typeInfos.filter(_._2._1 <= currentGeneration).toSeq.map(_._1)

      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val newTypeInfos = blockers.flatMap(id => typeInfos.get(id).map(id -> _))
      typeInfos --= blockers

      for ((blocker, (gen, _, _, tps)) <- newTypeInfos; info @ TemplateTypeInfo(tadt, arg) <- tps) {
        val template = mkTemplate(tadt.toType)
        newClauses ++= template.instantiate(blocker, arg)
      }

      newClauses.toSeq
    }
  }
}
