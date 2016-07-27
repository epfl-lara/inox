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
  case class TemplateTypeInfo(tcd: TypedAbstractClassDef, arg: Encoded) {
    override def toString = tcd.toType.asString + "(" + arg.asString + ")"
  }

  private val cache: MutableMap[Type, DatatypeTemplate] = MutableMap.empty
  private def mkTemplate(tpe: Type): DatatypeTemplate = cache.getOrElseUpdate(tpe, DatatypeTemplate(tpe))

  def registerSymbol(start: Encoded, sym: Encoded, tpe: Type): Clauses = {
    mkTemplate(tpe).instantiate(start, sym)
  }

  object DatatypeTemplate {

    private val requireChecking: MutableSet[TypedClassDef] = MutableSet.empty
    private val requireCache: MutableMap[Type, Boolean] = MutableMap.empty

    private def requireTypeUnrolling(tpe: Type): Boolean = requireCache.get(tpe) match {
      case Some(res) => res
      case None =>
        val res = tpe match {
          case ft: FunctionType => true
          case ct: ClassType => ct.tcd match {
            case tccd: TypedCaseClassDef => tccd.parent.isDefined
            case tcd if requireChecking(tcd.root) => false
            case tcd =>
              requireChecking += tcd.root
              val classTypes = tcd.root +: (tcd.root match {
                case (tacd: TypedAbstractClassDef) => tacd.descendants
                case _ => Seq.empty
              })

              classTypes.exists(ct => ct.hasInvariant || (ct match {
                case tccd: TypedCaseClassDef => tccd.fieldsTypes.exists(requireTypeUnrolling)
                case _ => false
              }))
          }

          case BooleanType | UnitType | CharType | IntegerType |
               RealType | StringType | (_: BVType) | (_: TypeParameter) => false

          case NAryType(tpes, _) => tpes.exists(requireTypeUnrolling)
        }

        requireCache += tpe -> res
        res
    }

    private case class FreshFunction(expr: Expr) extends Expr with Extractable {
      def getType(implicit s: Symbols) = BooleanType
      val extract = Some(Seq(expr), (exprs: Seq[Expr]) => FreshFunction(exprs.head))
    }

    private case class InductiveType(tcd: TypedAbstractClassDef, expr: Expr) extends Expr with Extractable {
      def getType(implicit s: Symbols) = BooleanType
      val extract = Some(Seq(expr), (exprs: Seq[Expr]) => InductiveType(tcd, exprs.head))
    }

    private def typeUnroller(expr: Expr): Expr = expr.getType match {
      case tpe if !requireTypeUnrolling(tpe) =>
        BooleanLiteral(true)

      case ct: ClassType =>
        val tcd = ct.tcd

        val inv: Seq[Expr] = if (tcd.hasInvariant) {
          Seq(tcd.invariant.get.applied(Seq(expr)))
        } else {
          Seq.empty
        }

        def unrollFields(tcd: TypedCaseClassDef): Seq[Expr] = tcd.fields.map { vd =>
          val tpe = tcd.toType
          typeUnroller(CaseClassSelector(tpe, AsInstanceOf(expr, tpe), vd.id))
        }

        val fields: Seq[Expr] = if (tcd != tcd.root) {
          IsInstanceOf(expr, tcd.toType) +: unrollFields(tcd.toCase)
        } else {
          val isInductive = tcd.cd match {
            case acd: AbstractClassDef => acd.isInductive
            case _ => false
          }

          if (!isInductive) {
            val matchers = tcd.root match {
              case (act: TypedAbstractClassDef) => act.descendants
              case (cct: TypedCaseClassDef) => Seq(cct)
            }

            val thens = matchers.map(tcd => tcd -> andJoin(unrollFields(tcd)))

            if (thens.forall(_._2 == BooleanLiteral(true))) {
              Seq.empty
            } else {
              val (ifs :+ last) = thens
              Seq(ifs.foldRight(last._2) { case ((tcd, thenn), res) =>
                IfExpr(IsInstanceOf(expr, tcd.toType), thenn, res)
              })
            }
          } else {
            Seq(InductiveType(tcd.toAbstract, expr))
          }
        }

        andJoin(inv ++ fields)

      case TupleType(tpes) =>
        andJoin(tpes.zipWithIndex.map(p => typeUnroller(TupleSelect(expr, p._2 + 1))))

      case FunctionType(_, _) =>
        FreshFunction(expr)

      case _ => scala.sys.error("TODO")
    }

    def apply(tpe: Type): DatatypeTemplate = {
      val v = Variable(FreshIdentifier("x", true), tpe)
      val expr = typeUnroller(v)

      val pathVar = Variable(FreshIdentifier("b", true), BooleanType)

      var condVars = Map[Variable, Encoded]()
      var condTree = Map[Variable, Set[Variable]](pathVar -> Set.empty).withDefaultValue(Set.empty)
      def storeCond(pathVar: Variable, v: Variable): Unit = {
        condVars += v -> encodeSymbol(v)
        condTree += pathVar -> (condTree(pathVar) + v)
      }

      var guardedExprs = Map[Variable, Seq[Expr]]()
      def storeGuarded(pathVar: Variable, expr: Expr): Unit = {
        val prev = guardedExprs.getOrElse(pathVar, Nil)
        guardedExprs += pathVar -> (expr +: prev)
      }

      def iff(e1: Expr, e2: Expr): Unit = storeGuarded(pathVar, Equals(e1, e2))

      def requireDecomposition(e: Expr): Boolean = exprOps.exists {
        case _: FunctionInvocation => true
        case _: InductiveType => true
        case _ => false
      } (e)

      def rec(pathVar: Variable, expr: Expr): Unit = expr match {
        case i @ IfExpr(cond, thenn, elze) if requireDecomposition(i) =>
          val newBool1: Variable = Variable(FreshIdentifier("b", true), BooleanType)
          val newBool2: Variable = Variable(FreshIdentifier("b", true), BooleanType)

          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)

          iff(and(pathVar, cond), newBool1)
          iff(and(pathVar, not(cond)), newBool2)

          rec(newBool1, thenn)
          rec(newBool2, elze)

        case a @ And(es) if requireDecomposition(a) =>
          val partitions = SeqUtils.groupWhile(es)(!requireDecomposition(_))
          for (e <- partitions.map(andJoin)) rec(pathVar, e)

        case _ =>
          storeGuarded(pathVar, expr)
      }

      rec(pathVar, expr)

      val (idT, pathVarT) = (encodeSymbol(v), encodeSymbol(pathVar))
      val encoder: Expr => Encoded = encodeExpr(condVars + (v -> idT) + (pathVar -> pathVarT))

      var clauses: Clauses = Seq.empty
      var calls: CallBlockers  = Map.empty
      var types: Map[Encoded, Set[TemplateTypeInfo]] = Map.empty
      var functions: Functions = Set.empty

      for ((b, es) <- guardedExprs) {
        var callInfos : Set[Call]             = Set.empty
        var typeInfos : Set[TemplateTypeInfo] = Set.empty

        for (e <- es) {
          val collected = collectWithPaths {
            case expr @ (_: InductiveType | _: FreshFunction) => expr
          } (e)

          def clean(e: Expr) = exprOps.postMap {
            case _: InductiveType => Some(BooleanLiteral(true))
            case _: FreshFunction => Some(BooleanLiteral(true))
            case _ => None
          } (e)

          functions ++= collected.collect { case (FreshFunction(f), path) =>
            val tpe = bestRealType(f.getType).asInstanceOf[FunctionType]
            val cleanPath = path.map(clean)
            (encoder(and(b, cleanPath.toPath)), tpe, encoder(f))
          }

          typeInfos ++= collected.collect { case (InductiveType(tcd, e), path) =>
            assert(path.isEmpty, "Inductive datatype unfolder should be implied directly by the blocker")
            TemplateTypeInfo(tcd, encoder(e))
          }

          val cleanExpr = clean(e)
          callInfos ++= firstOrderCallsOf(cleanExpr).map { case (id, tps, args) =>
            Call(getFunction(id, tps), args.map(arg => Left(encoder(arg))))
          }

          clauses :+= encoder(Implies(b, cleanExpr))
        }

        if (typeInfos.nonEmpty) types += encoder(b) -> typeInfos
        if (callInfos.nonEmpty) calls += encoder(b) -> callInfos
      }

      new DatatypeTemplate(pathVar -> pathVarT, idT, condVars, condTree, clauses, calls, types, functions)
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
      val blockers = typeInfos.filter(_._2._1 <= currentGeneration).toSeq.map(_._1)

      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val newTypeInfos = blockers.flatMap(id => typeInfos.get(id).map(id -> _))
      typeInfos --= blockers

      for ((blocker, (gen, _, _, tps)) <- newTypeInfos; info @ TemplateTypeInfo(tcd, arg) <- tps) {
        val template = mkTemplate(tcd.toType)
        newClauses ++= template.instantiate(blocker, arg)
      }

      newClauses.toSeq
    }
  }
}
