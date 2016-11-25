/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import scala.collection.mutable.{Map => MutableMap}

trait TemplateGenerator { self: Templates =>
  import program._
  import program.trees._
  import program.symbols._

  protected type TemplateClauses = (
    Map[Variable, Encoded],
    Map[Variable, Encoded],
    Map[Variable, Set[Variable]],
    Map[Variable, Seq[Expr]],
    Seq[Expr],
    Seq[LambdaTemplate],
    Seq[QuantificationTemplate]
  )

  protected def emptyClauses: TemplateClauses =
    (Map.empty, Map.empty, Map.empty, Map.empty, Seq.empty, Seq.empty, Seq.empty)

  protected implicit class ClausesWrapper(clauses: TemplateClauses) {
    def ++(that: TemplateClauses): TemplateClauses = {
      val (thisConds, thisExprs, thisTree, thisGuarded, thisEqs, thisLambdas, thisQuants) = clauses
      val (thatConds, thatExprs, thatTree, thatGuarded, thatEqs, thatLambdas, thatQuants) = that

      (thisConds ++ thatConds, thisExprs ++ thatExprs,
        thisTree merge thatTree, thisGuarded merge thatGuarded,
        thisEqs ++ thatEqs, thisLambdas ++ thatLambdas, thisQuants ++ thatQuants)
    }

    def +(pair: (Variable, Expr)): TemplateClauses = {
      val (thisConds, thisExprs, thisTree, thisGuarded, thisEqs, thisLambdas, thisQuants) = clauses
      (thisConds, thisExprs, thisTree, thisGuarded merge pair, thisEqs, thisLambdas, thisQuants)
    }
  }

  private def isSimple(expr: Expr): Boolean = {
    exprOps.isSimple(expr) && !exprOps.exists {
      case Equals(e1, e2) => unrollEquality(e1.getType)
      case _ => false
    } (expr)
  }

  def mkClauses(pathVar: Variable, expr: Expr, substMap: Map[Variable, Encoded], polarity: Option[Boolean] = None): TemplateClauses = {
    val (p, (condVars, exprVars, condTree, guardedExprs, eqs, lambdas, quantifications)) = mkExprClauses(pathVar, expr, substMap, polarity)
    val allGuarded = guardedExprs + (pathVar -> (p +: guardedExprs.getOrElse(pathVar, Seq.empty)))
    (condVars, exprVars, condTree, allGuarded, eqs, lambdas, quantifications)
  }

  protected def mkExprStructure(
    pathVar: Variable,
    expr: Expr,
    substMap: Map[Variable, Encoded],
    onlySimple: Boolean = false
  ): (Expr, TemplateStructure, Map[Variable, Encoded]) = {
    val (struct, depsByScope) = normalizeStructure(expr, onlySimple = onlySimple)
    val deps = depsByScope.toMap

    lazy val isNormalForm: Boolean = {
      def extractBody(e: Expr): (Seq[ValDef], Expr) = e match {
        case Lambda(args, body) =>
          val (nextArgs, nextBody) = extractBody(body)
          (args ++ nextArgs, nextBody)
        case _ => (Seq.empty, e)
      }

      val (params, app) = extractBody(struct)
      ApplicationExtractor.extract(app, simplify) match {
        case Some((caller: Variable, args)) =>
          !app.getType.isInstanceOf[FunctionType] &&
          (params.map(_.toVariable) == args) &&
          (deps.get(caller) match {
            case Some(_: Application | _: FunctionInvocation | _: Variable | _: ADTSelector) => true
            case _ => false
          })
        case _ => false
      }
    }

    val (depSubst, basePointers, (depConds, depExprs, depTree, depGuarded, depEqs, depLambdas, depQuants)) =
      depsByScope.foldLeft[(Map[Variable, Encoded], Map[Encoded, Encoded], TemplateClauses)](
        (substMap, Map.empty, emptyClauses)
      ) { case ((depSubst, pointers, clsSet), (v, expr)) =>
          if (!isSimple(expr)) {
            val normalExpr = if (!isNormalForm) simplifyHOFunctions(expr) else expr
            val (e, cls @ (conds, exprs, _, _, _, lmbds, quants)) = mkExprClauses(pathVar, normalExpr, depSubst)
            val clauseSubst = depSubst ++ conds ++ exprs ++ lmbds.map(_.ids) ++ quants.flatMap(_.mapping)
            val encoder = mkEncoder(clauseSubst) _
            (depSubst + (v -> encoder(e)), Template.lambdaPointers(encoder)(e), clsSet ++ cls)
          } else {
            val encoder = mkEncoder(depSubst) _
            (depSubst + (v -> encoder(expr)), Template.lambdaPointers(encoder)(expr), clsSet)
          }
      }

    val (depClauses, depCalls, depApps, depMatchers, depEqualities, depPointers, _) = Template.encode(
      pathVar -> substMap(pathVar), Seq.empty, depConds,
      depExprs, depGuarded, depEqs, depLambdas, depQuants, depSubst)

    val sortedDeps = exprOps.variablesOf(struct).map(v => v -> deps(v)).toSeq.sortBy(_._1.id.uniqueName)
    val dependencies = sortedDeps.map(p => depSubst(p._1))

    val structure = new TemplateStructure(struct, dependencies, TemplateContents(
      pathVar -> substMap(pathVar), Seq.empty, depConds, depExprs, depTree, depClauses,
      depCalls, depApps, depMatchers, depEqualities, depLambdas, depQuants, basePointers ++ depPointers))

    val res = if (isNormalForm) expr else struct
    (res, structure, depSubst)
  }

  protected def mkExprClauses(
    pathVar: Variable,
    expr: Expr,
    substMap: Map[Variable, Encoded],
    polarity: Option[Boolean] = None
  ): (Expr, TemplateClauses) = {
    val initVar = pathVar

    var condVars = Map[Variable, Encoded]()
    var condTree = Map[Variable, Set[Variable]](pathVar -> Set.empty).withDefaultValue(Set.empty)
    def storeCond(pathVar: Variable, id: Variable) : Unit = {
      condVars += id -> encodeSymbol(id)
      condTree += pathVar -> (condTree(pathVar) + id)
    }

    @inline def encodedCond(id: Variable): Encoded = substMap.getOrElse(id, condVars(id))

    var exprVars = Map[Variable, Encoded]()
    @inline def storeExpr(id: Variable) : Unit = exprVars += id -> encodeSymbol(id)

    // Represents clauses of the form:
    //    id => expr && ... && expr
    var guardedExprs = Map[Variable, Seq[Expr]]()
    def storeGuarded(guardVar: Variable, expr: Expr) : Unit = {
      assert(expr.getType == BooleanType, expr.asString + " is not of type Boolean. " + explainTyping(expr))

      val prev = guardedExprs.getOrElse(guardVar, Nil)
      guardedExprs += guardVar -> (expr +: prev)
    }

    // Represents equations (simple formulas)
    var eqs = Seq[Expr]()
    @inline def iff(e1: Expr, e2: Expr): Unit = eqs :+= Equals(e1, e2)

    var lambdas = Seq[LambdaTemplate]()
    @inline def registerLambda(lambda: LambdaTemplate) : Unit = lambdas :+= lambda

    var quantifications = Seq[QuantificationTemplate]()
    @inline def registerQuantification(quantification: QuantificationTemplate): Unit =
      quantifications :+= quantification

    @inline def localSubst: Map[Variable, Encoded] = substMap ++ condVars ++ exprVars ++ lambdas.map(_.ids)

    def rec(pathVar: Variable, expr: Expr, pol: Option[Boolean]): Expr = expr match {
      case a @ Assume(cond, body) =>
        val e = rec(pathVar, cond, Some(true))
        storeGuarded(pathVar, e)
        rec(pathVar, body, pol)

      case c @ Choose(res, pred) =>
        val newExpr = res.toVariable.freshen
        storeExpr(newExpr)

        val p = rec(pathVar, exprOps.replace(Map(res.toVariable -> newExpr), pred), Some(true))
        storeGuarded(pathVar, p)
        newExpr

      case l @ Let(i, e: Lambda, b) =>
        val re = rec(pathVar, e, None) // guaranteed variable!
        val rb = rec(pathVar, exprOps.replace(Map(i.toVariable -> re), b), pol)
        rb

      case l @ Let(i, e, b) =>
        val newExpr : Variable = Variable(FreshIdentifier("lt", true), i.getType)
        storeExpr(newExpr)
        val re = rec(pathVar, e, None)
        storeGuarded(pathVar, Equals(newExpr, re))
        val rb = rec(pathVar, exprOps.replace(Map(i.toVariable -> newExpr), b), pol)
        rb

      case n @ Not(e) =>
        Not(rec(pathVar, e, pol.map(!_)))

      case i @ Implies(lhs, rhs) =>
        if (!isSimple(i)) {
          rec(pathVar, Or(Not(lhs), rhs), pol)
        } else {
          implies(rec(pathVar, lhs, None), rec(pathVar, rhs, None))
        }

      case a @ And(parts) =>
        val partitions = SeqUtils.groupWhile(parts)(isSimple)
        partitions.map(andJoin) match {
          case Seq(e) => e
          case seq =>
            val newExpr: Variable = Variable(FreshIdentifier("e", true), BooleanType)
            storeExpr(newExpr)

            def recAnd(pathVar: Variable, partitions: Seq[Expr]): Unit = partitions match {
              case x :: Nil =>
                storeGuarded(pathVar, Equals(newExpr, rec(pathVar, x, pol)))

              case x :: xs =>
                val newRes: Variable = Variable(FreshIdentifier("res", true), BooleanType)
                storeExpr(newRes)

                val xrec = rec(pathVar, x, pol)
                storeGuarded(pathVar, Equals(newRes, xrec))

                val newBool: Variable = Variable(FreshIdentifier("b", true), BooleanType)
                storeCond(pathVar, newBool)

                storeGuarded(pathVar, implies(not(newRes), not(newExpr)))
                iff(and(pathVar, newRes), newBool)

                recAnd(newBool, xs)

              case Nil => scala.sys.error("Should never happen!")
            }

            recAnd(pathVar, seq)
            newExpr
        }

      case o @ Or(parts) =>
        val partitions = SeqUtils.groupWhile(parts)(isSimple)
        partitions.map(orJoin) match {
          case Seq(e) => e
          case seq =>
            val newExpr: Variable = Variable(FreshIdentifier("e", true), BooleanType)
            storeExpr(newExpr)

            def recOr(pathVar: Variable, partitions: Seq[Expr]): Unit = partitions match {
              case x :: Nil =>
                storeGuarded(pathVar, Equals(newExpr, rec(pathVar, x, None)))

              case x :: xs =>
                val newRes: Variable = Variable(FreshIdentifier("res", true), BooleanType)
                storeExpr(newRes)

                val xrec = rec(pathVar, x, pol)
                storeGuarded(pathVar, Equals(newRes, xrec))

                val newBool: Variable = Variable(FreshIdentifier("b", true), BooleanType)
                storeCond(pathVar, newBool)

                storeGuarded(pathVar, implies(newRes, newExpr))
                iff(and(pathVar, not(newRes)), newBool)

                recOr(newBool, xs)

              case Nil => scala.sys.error("Should never happen!")
            }

            recOr(pathVar, seq)
            newExpr
        }

      case i @ IfExpr(cond, thenn, elze) => {
        if (isSimple(i)) {
          i
        } else {
          val newBool1 : Variable = Variable(FreshIdentifier("b", true), BooleanType)
          val newBool2 : Variable = Variable(FreshIdentifier("b", true), BooleanType)
          val newExpr  : Variable = Variable(FreshIdentifier("e", true), i.getType)
          val condVar  : Variable = Variable(FreshIdentifier("c", true), BooleanType)

          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)
          storeExpr(newExpr)
          storeExpr(condVar)

          val crec = rec(pathVar, cond, None)
          val trec = rec(newBool1, thenn, None)
          val erec = rec(newBool2, elze, None)

          storeGuarded(pathVar, Equals(condVar, crec))
          iff(and(pathVar, condVar), newBool1)
          iff(and(pathVar, not(condVar)), newBool2)

          storeGuarded(newBool1, Equals(newExpr, trec))
          storeGuarded(newBool2, Equals(newExpr, erec))
          newExpr
        }
      }

      case l: Lambda =>
        val (assumptions, without: Lambda) = liftAssumptions(l)

        for (a <- assumptions) {
          rec(pathVar, a, Some(true))
        }

        val template = LambdaTemplate(pathVar -> encodedCond(pathVar), without, localSubst)
        registerLambda(template)
        template.ids._1

      case f: Forall =>
        val (assumptions, without: Forall) = liftAssumptions(f)

        for (a <- assumptions) {
          rec(pathVar, a, Some(true))
        }

        val argsSet = without.args.toSet
        val TopLevelAnds(conjuncts) = without.body

        val conjunctQs = conjuncts.map { conj =>
          val conjArgs: Seq[ValDef] = {
            var vds: Seq[ValDef] = Seq.empty
            exprOps.preTraversal { case v: Variable if argsSet(v.toVal) => vds :+= v.toVal case _ => } (conj)
            vds.distinct
          }

          val (optVar, template) = QuantificationTemplate(pathVar -> encodedCond(pathVar), pol, without, localSubst)
          registerQuantification(template)
          optVar.getOrElse(BooleanLiteral(true))
        }

        andJoin(conjunctQs)

      case Operator(as, r) => r(as.map(a => rec(pathVar, a, None)))
    }

    val p = rec(pathVar, expr, polarity)
    (p, (condVars, exprVars, condTree, guardedExprs, eqs, lambdas, quantifications))
  }
}
