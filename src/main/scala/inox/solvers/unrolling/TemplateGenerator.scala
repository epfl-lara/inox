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

  type SelectorPath = Seq[Either[Identifier, Int]]
  private val cache: MutableMap[(TypedFunDef, SelectorPath), FunctionTemplate] = MutableMap.empty

  def mkTemplate(tfd: TypedFunDef, path: SelectorPath): FunctionTemplate = {
    if (cache contains (tfd -> path)) {
      return cache(tfd -> path)
    }

    val lambdaBody: Expr = {
      def rec(e: Expr, path: SelectorPath): Expr = (e, path) match {
        case (ADT(tpe, es), Left(id) +: tail) =>
          rec(es(tpe.getADT.toConstructor.definition.selectorID2Index(id)), tail)
        case (Tuple(es), Right(i) +: tail) =>
          rec(es(i - 1), tail)
        case _ => e
      }

      rec(simplifyFormula(tfd.fullBody, simplify), path)
    }

    val funDefArgs: Seq[Variable] = tfd.params.map(_.toVariable)
    val lambdaArguments: Seq[Variable] = lambdaArgs(lambdaBody)
    val invocation: Expr = {
      def rec(e: Expr, path: SelectorPath): Expr = path match {
        case Left(id) +: tail => rec(ADTSelector(e, id), tail)
        case Right(i) +: tail => rec(TupleSelect(e, i), tail)
        case _ => e
      }

      rec(tfd.applied(funDefArgs), path)
    }

    val invocationEqualsBody : Seq[Expr] =
      liftedEquals(invocation, lambdaBody, lambdaArguments) :+ Equals(invocation, lambdaBody)

    val start : Variable = Variable(FreshIdentifier("start", true), BooleanType)
    val pathVar : (Variable, Encoded) = start -> encodeSymbol(start)

    val allArguments : Seq[Variable] = funDefArgs ++ lambdaArguments
    val arguments : Seq[(Variable, Encoded)] = allArguments.map(id => id -> encodeSymbol(id))

    val substMap : Map[Variable, Encoded] = arguments.toMap + pathVar

    val (condVars, exprVars, condTree, guardedExprs, eqs, lambdas, quantifications) =
      invocationEqualsBody.foldLeft(emptyClauses)((clsSet, cls) => clsSet ++ mkClauses(start, cls, substMap))

    val template = FunctionTemplate(tfd, path, pathVar, arguments,
      condVars, exprVars, condTree, guardedExprs, eqs, lambdas, quantifications)
    cache += (tfd, path) -> template
    template
  }

  private def lambdaArgs(expr: Expr): Seq[Variable] = expr match {
    case Lambda(args, body) => args.map(_.toVariable.freshen) ++ lambdaArgs(body)
    case Assume(pred, body) => lambdaArgs(body)
    case IsTyped(_, _: FunctionType) => sys.error("Only applicable on lambda/assume chains")
    case _ => Seq.empty
  }

  private def liftedEquals(invocation: Expr, body: Expr, args: Seq[Variable], inlineFirst: Boolean = false): Seq[Expr] = {
    def rec(i: Expr, b: Expr, args: Seq[Variable], inline: Boolean): Seq[Expr] = i.getType match {
      case FunctionType(from, to) =>
        def apply(e: Expr, es: Seq[Expr]): Expr = e match {
          case _: Lambda if inline => application(e, es)
          case Assume(pred, l: Lambda) if inline => Assume(pred, application(l, es))
          case _ => Application(e, es)
        }

        val (currArgs, nextArgs) = args.splitAt(from.size)
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

      case n @ Not(e) =>
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

      case l: Lambda =>
        val idArgs : Seq[Variable] = lambdaArgs(l)
        val trArgs : Seq[Encoded] = idArgs.map(id => substMap.getOrElse(id, encodeSymbol(id)))

        val (assumptions, without) = liftAssumptions(l)

        for (a <- assumptions) {
          rec(pathVar, a, Some(true))
        }

        val (realLambda, structure, depSubst) = recStructure(pathVar, l)

        val depClosures = exprOps.variablesOf(l).flatMap(lambdaVars.get)

        val lid = Variable(FreshIdentifier("lambda", true), l.getType)
        val clauses = liftedEquals(lid, realLambda, idArgs, inlineFirst = true)

        val clauseSubst: Map[Variable, Encoded] = depSubst ++ (idArgs zip trArgs)
        val (lambdaConds, lambdaExprs, lambdaTree, lambdaGuarded, lambdaEqs, lambdaTemplates, lambdaQuants) =
          clauses.foldLeft(emptyClauses)((clsSet, cls) => clsSet ++ mkClauses(pathVar, cls, clauseSubst))

        val ids: (Variable, Encoded) = lid -> storeLambda(lid)

        val template = LambdaTemplate(ids, pathVar -> encodedCond(pathVar),
          idArgs zip trArgs, lambdaConds, lambdaExprs, lambdaTree,
          lambdaGuarded, lambdaEqs, lambdaTemplates, lambdaQuants, structure, depClosures, depSubst, l)
        registerLambda(template)
        lid

      case f: Forall =>
        val (assumptions, Forall(args, body)) = liftAssumptions(f)
        val argsSet = args.toSet

        for (a <- assumptions) {
          rec(pathVar, a, Some(true))
        }

        val TopLevelAnds(conjuncts) = body

        val conjunctQs = conjuncts.map { conj =>
          val conjArgs: Seq[ValDef] = {
            var vds: Seq[ValDef] = Seq.empty
            exprOps.preTraversal { case v: Variable if argsSet(v.toVal) => vds :+= v.toVal case _ => } (conj)
            vds.distinct
          }

          val (Forall(args, body), structure, depSubst) = recStructure(pathVar, Forall(conjArgs, conj))

          val quantifiers = args.map(_.toVariable).toSet
          val idQuantifiers : Seq[Variable] = quantifiers.toSeq
          val trQuantifiers : Seq[Encoded] = conjArgs.map(v => encodeSymbol(v.toVariable))

          val clauseSubst: Map[Variable, Encoded] = depSubst ++ (idQuantifiers zip trQuantifiers)
          val (p, (qConds, qExprs, qTree, qGuarded, qEqs, qLambdas, qQuants)) = mkExprClauses(pathVar, body, clauseSubst)

          val (optVar, template) = QuantificationTemplate(pathVar -> encodedCond(pathVar),
            pol, p, idQuantifiers zip trQuantifiers, qConds, qExprs, qTree, qGuarded, qEqs, qLambdas, qQuants,
            structure, depSubst, Forall(conjArgs, conj))
          registerQuantification(template)
          optVar.getOrElse(BooleanLiteral(true))
        }

        andJoin(conjunctQs)

      case Operator(as, r) => r(as.map(a => rec(pathVar, a, None)))
    }

    def recStructure(pathVar: Variable, expr: Expr): (Expr, TemplateStructure, Map[Variable, Encoded]) = {
      val (assumptions, without) = liftAssumptions(expr)

      for (a <- assumptions) {
        rec(pathVar, a, Some(true))
      }

      val (struct, deps) = normalizeStructure(without)
      val sortedDeps = exprOps.variablesOf(struct).map(v => v -> deps(v)).toSeq.sortBy(_._1.id.uniqueName)

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

      val depsByScope: Seq[(Variable, Expr)] = {
        def rec(v: Variable): Seq[Variable] =
          (exprOps.variablesOf(deps(v)) & deps.keySet - v).toSeq.flatMap(rec) :+ v
        deps.keys.toSeq.flatMap(rec).distinct.map(v => v -> deps(v))
      }

      val localSubst: Map[Variable, Encoded] = substMap ++ condVars ++ exprVars ++ lambdaVars
      val (depSubst, basePointers, (depConds, depExprs, depTree, depGuarded, depEqs, depLambdas, depQuants)) =
        depsByScope.foldLeft[(Map[Variable, Encoded], Map[Encoded, Encoded], TemplateClauses)](
          (localSubst, Map.empty, emptyClauses)
        ) { case ((depSubst, pointers, clsSet), (v, expr)) =>
            if (!exprOps.isSimple(expr)) {
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

      val (depClauses, depCalls, depApps, depMatchers, depPointers, _) = Template.encode(
        pathVar -> encodedCond(pathVar), Seq.empty,
        depConds, depExprs, depGuarded, depEqs, depLambdas, depQuants, depSubst)

      val dependencies = sortedDeps.map(p => depSubst(p._1))

      val structure = new TemplateStructure(struct, dependencies,
        pathVar -> encodedCond(pathVar), depConds, depExprs, depTree,
        depClauses, depCalls, depApps, depMatchers, depLambdas, depQuants, basePointers ++ depPointers)

      val res = if (isNormalForm) expr else struct
      (res, structure, depSubst)
    }

    val p = rec(pathVar, expr, polarity)
    (p, (condVars, exprVars, condTree, guardedExprs, eqs, lambdas, quantifications))
  }
}
