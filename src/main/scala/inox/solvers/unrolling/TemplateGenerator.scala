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

  private type TemplateClauses = (
    Map[Variable, Encoded],
    Map[Variable, Encoded],
    Map[Variable, Set[Variable]],
    Map[Variable, Seq[Expr]],
    Seq[Expr],
    Seq[LambdaTemplate],
    Seq[QuantificationTemplate]
  )

  private def emptyClauses: TemplateClauses =
    (Map.empty, Map.empty, Map.empty, Map.empty, Seq.empty, Seq.empty, Seq.empty)

  private implicit class ClausesWrapper(clauses: TemplateClauses) {
    def ++(that: TemplateClauses): TemplateClauses = {
      val (thisConds, thisExprs, thisTree, thisGuarded, thisEqs, thisLambdas, thisQuants) = clauses
      val (thatConds, thatExprs, thatTree, thatGuarded, thatEqs, thatLambdas, thatQuants) = that

      (thisConds ++ thatConds, thisExprs ++ thatExprs,
        thisTree merge thatTree, thisGuarded merge thatGuarded,
        thisEqs ++ thatEqs, thisLambdas ++ thatLambdas, thisQuants ++ thatQuants)
    }
  }

  private val cache: MutableMap[TypedFunDef, FunctionTemplate] = MutableMap.empty

  def mkTemplate(tfd: TypedFunDef): FunctionTemplate = {
    if (cache contains tfd) {
      return cache(tfd)
    }

    val lambdaBody : Expr = simplifyHOFunctions(tfd.fullBody)

    val funDefArgs: Seq[Variable] = tfd.params.map(_.toVariable)
    val lambdaArguments: Seq[Variable] = lambdaArgs(lambdaBody)
    val invocation : Expr = tfd.applied(funDefArgs)

    val invocationEqualsBody : Seq[Expr] =
      liftedEquals(invocation, lambdaBody, lambdaArguments) :+ Equals(invocation, lambdaBody)

    val start : Variable = Variable(FreshIdentifier("start", true), BooleanType)
    val pathVar : (Variable, Encoded) = start -> encodeSymbol(start)

    val allArguments : Seq[Variable] = funDefArgs ++ lambdaArguments
    val arguments : Seq[(Variable, Encoded)] = allArguments.map(id => id -> encodeSymbol(id))

    val substMap : Map[Variable, Encoded] = arguments.toMap + pathVar

    val (condVars, exprVars, condTree, guardedExprs, eqs, lambdas, quantifications) =
      invocationEqualsBody.foldLeft(emptyClauses)((clsSet, cls) => clsSet ++ mkClauses(start, cls, substMap))

    val template = FunctionTemplate(tfd, pathVar, arguments,
      condVars, exprVars, condTree, guardedExprs, eqs, lambdas, quantifications)
    cache += tfd -> template
    template
  }

  private def lambdaArgs(expr: Expr): Seq[Variable] = expr match {
    case Lambda(args, body) => args.map(_.toVariable.freshen) ++ lambdaArgs(body)
    case IsTyped(_, _: FunctionType) => sys.error("Only applicable on lambda chains")
    case _ => Seq.empty
  }

  private def liftedEquals(invocation: Expr, body: Expr, args: Seq[Variable], inlineFirst: Boolean = false): Seq[Expr] = {
    def rec(i: Expr, b: Expr, args: Seq[Variable], inline: Boolean): Seq[Expr] = i.getType match {
      case FunctionType(from, to) =>
        val (currArgs, nextArgs) = args.splitAt(from.size)
        val apply = if (inline) application _ else Application
        val (appliedInv, appliedBody) = (apply(i, currArgs), apply(b, currArgs))
        rec(appliedInv, appliedBody, nextArgs, false) :+ Equals(appliedInv, appliedBody)
      case _ =>
        assert(args.isEmpty, "liftedEquals should consume all provided arguments")
        Seq.empty
    }

    rec(invocation, body, args, inlineFirst)
  }

  def mkClauses(pathVar: Variable, expr: Expr, substMap: Map[Variable, Encoded], polarity: Option[Boolean] = None): TemplateClauses = {
    val (p, (condVars, exprVars, condTree, guardedExprs, eqs, lambdas, quantifications)) = mkExprClauses(pathVar, expr, substMap, polarity)
    val allGuarded = guardedExprs + (pathVar -> (p +: guardedExprs.getOrElse(pathVar, Seq.empty)))
    (condVars, exprVars, condTree, allGuarded, eqs, lambdas, quantifications)
  }

  private def mkExprClauses(pathVar: Variable, expr: Expr, substMap: Map[Variable, Encoded], polarity: Option[Boolean] = None): (Expr, TemplateClauses) = {
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

    var lambdaVars = Map[Variable, Encoded]()
    @inline def storeLambda(id: Variable): Encoded = {
      val idT = encodeSymbol(id)
      lambdaVars += id -> idT
      idT
    }

    var quantifications = Seq[QuantificationTemplate]()
    @inline def registerQuantification(quantification: QuantificationTemplate): Unit =
      quantifications :+= quantification

    var lambdas = Seq[LambdaTemplate]()
    @inline def registerLambda(lambda: LambdaTemplate) : Unit = lambdas :+= lambda

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

      case n @ Not(e) if n.getType == BooleanType =>
        Not(rec(pathVar, e, pol.map(!_)))

      case i @ Implies(lhs, rhs) =>
        if (!exprOps.isSimple(i)) {
          rec(pathVar, Or(Not(lhs), rhs), pol)
        } else {
          implies(rec(pathVar, lhs, None), rec(pathVar, rhs, None))
        }

      case a @ And(parts) =>
        val partitions = SeqUtils.groupWhile(parts)(exprOps.isSimple)
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
        val partitions = SeqUtils.groupWhile(parts)(exprOps.isSimple)
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
        if(exprOps.isSimple(i)) {
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

      case l @ Lambda(args, body) =>
        val idArgs : Seq[Variable] = lambdaArgs(l)
        val trArgs : Seq[Encoded] = idArgs.map(id => substMap.getOrElse(id, encodeSymbol(id)))

        val lid = Variable(FreshIdentifier("lambda", true), bestRealType(l.getType))
        val clauses = liftedEquals(lid, l, idArgs, inlineFirst = true)

        val localSubst: Map[Variable, Encoded] = substMap ++ condVars ++ exprVars ++ lambdaVars
        val clauseSubst: Map[Variable, Encoded] = localSubst ++ (idArgs zip trArgs)
        val (lambdaConds, lambdaExprs, lambdaTree, lambdaGuarded, lambdaEqs, lambdaTemplates, lambdaQuants) =
          clauses.foldLeft(emptyClauses)((clsSet, cls) => clsSet ++ mkClauses(pathVar, cls, clauseSubst))

        val ids: (Variable, Encoded) = lid -> storeLambda(lid)

        val (struct, deps) = normalizeStructure(l)
        val sortedDeps = deps.toSeq.sortBy(_._1.id.uniqueName)

        val (dependencies, (depConds, depExprs, depTree, depGuarded, depEqs, depLambdas, depQuants)) =
          sortedDeps.foldLeft[(Seq[Encoded], TemplateClauses)](Seq.empty -> emptyClauses) {
            case ((dependencies, clsSet), (id, expr)) =>
              if (!exprOps.isSimple(expr)) {
                val encoded = encodeSymbol(id)
                val (e, cls @ (_, _, _, _, _, lmbds, quants)) = mkExprClauses(pathVar, expr, localSubst)
                val clauseSubst = localSubst ++ lmbds.map(_.ids) ++ quants.flatMap(_.mapping)
                (dependencies :+ mkEncoder(clauseSubst)(e), clsSet ++ cls)
              } else {
                (dependencies :+ mkEncoder(localSubst)(expr), clsSet)
              }
          }

        val (depClauses, depCalls, depApps, depMatchers, _) = Template.encode(
          pathVar -> encodedCond(pathVar), Seq.empty,
          depConds, depExprs, depGuarded, depEqs, depLambdas, depQuants, localSubst)

        val depClosures: Seq[Encoded] = {
          val vars = exprOps.variablesOf(l)
          var cls: Seq[Variable] = Seq.empty
          exprOps.preTraversal { case v: Variable if vars(v) => cls :+= v case _ => } (l)
          cls.distinct.map(localSubst)
        }

        val structure = new LambdaStructure(
          struct, dependencies, pathVar -> encodedCond(pathVar), depClosures,
          depConds, depExprs, depTree, depClauses, depCalls, depApps, depMatchers, depLambdas, depQuants)

        val template = LambdaTemplate(ids, pathVar -> encodedCond(pathVar),
          idArgs zip trArgs, lambdaConds, lambdaExprs, lambdaTree,
          lambdaGuarded, lambdaEqs, lambdaTemplates, lambdaQuants, structure, localSubst, l)
        registerLambda(template)
        lid

      case f @ Forall(args, body) =>
        val TopLevelAnds(conjuncts) = body

        val conjunctQs = conjuncts.map { conjunct =>
          val vars = exprOps.variablesOf(conjunct)
          val quantifiers = args.map(_.toVariable).filter(vars).toSet

          val idQuantifiers : Seq[Variable] = quantifiers.toSeq
          val trQuantifiers : Seq[Encoded] = idQuantifiers.map(encodeSymbol)

          val localSubst: Map[Variable, Encoded] = substMap ++ condVars ++ exprVars ++ lambdaVars
          val clauseSubst: Map[Variable, Encoded] = localSubst ++ (idQuantifiers zip trQuantifiers)
          val (p, (qConds, qExprs, qTree, qGuarded, qEqs, qLambdas, qQuants)) = mkExprClauses(pathVar, conjunct, clauseSubst)

          val (optVar, template) = QuantificationTemplate(pathVar -> encodedCond(pathVar),
            pol, p, idQuantifiers zip trQuantifiers, qConds, qExprs, qTree, qGuarded, qEqs, qLambdas, qQuants,
            localSubst, Forall(quantifiers.toSeq.sortBy(_.id.uniqueName).map(_.toVal), conjunct))
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
