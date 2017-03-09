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
    Map[Variable, Encoded],
    Map[Variable, Set[Variable]],
    Map[Variable, Seq[Expr]],
    Seq[Expr],
    Equalities,
    Seq[LambdaTemplate],
    Seq[QuantificationTemplate]
  )

  protected def emptyClauses: TemplateClauses =
    (Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, Seq.empty, Map.empty, Seq.empty, Seq.empty)

  protected implicit class ClausesWrapper(clauses: TemplateClauses) {
    def ++(that: TemplateClauses): TemplateClauses = {
      val (thisConds, thisExprs, thisChooses, thisTree, thisGuarded, thisEqs, thisEqualities, thisLambdas, thisQuants) = clauses
      val (thatConds, thatExprs, thatChooses, thatTree, thatGuarded, thatEqs, thatEqualities, thatLambdas, thatQuants) = that

      (thisConds ++ thatConds, thisExprs ++ thatExprs, thisChooses ++ thatChooses,
        thisTree merge thatTree, thisGuarded merge thatGuarded, thisEqs ++ thatEqs,
        thisEqualities merge thatEqualities, thisLambdas ++ thatLambdas, thisQuants ++ thatQuants)
    }

    def +(pair: (Variable, Expr)): TemplateClauses = {
      val (thisConds, thisExprs, thisChooses, thisTree, thisGuarded, thisEqs, thisEqualities, thisLambdas, thisQuants) = clauses
      (thisConds, thisExprs, thisChooses, thisTree, thisGuarded merge pair, thisEqs, thisEqualities, thisLambdas, thisQuants)
    }

    def proj: (
      Map[Variable, Encoded],
      Map[Variable, Encoded],
      Map[Variable, Encoded],
      Map[Variable, Set[Variable]],
      Equalities,
      Seq[LambdaTemplate],
      Seq[QuantificationTemplate]
    ) = {
      val (thisConds, thisExprs, thisChooses, thisTree, thisGuarded, thisEqs, thisEqualities, thisLambdas, thisQuants) = clauses
      (thisConds, thisExprs, thisChooses, thisTree, thisEqualities, thisLambdas, thisQuants)
    }
  }

  private def isSimple(expr: Expr): Boolean = {
    exprOps.isSimple(expr) && !exprOps.exists {
      case Equals(e1, e2) => unrollEquality(e1.getType)
      case _ => false
    } (expr)
  }

  def mkClauses(pathVar: Variable, expr: Expr, substMap: Map[Variable, Encoded], polarity: Option[Boolean] = None): TemplateClauses = {
    val (p, (conds, exprs, chooses, tree, guarded, eqs, equalities, lambdas, quants)) = mkExprClauses(pathVar, expr, substMap, polarity)
    (conds, exprs, chooses, tree, guarded merge (pathVar -> p), eqs, equalities, lambdas, quants)
  }

  protected def mkExprStructure(
    pathVar: Variable,
    expr: Expr,
    substMap: Map[Variable, Encoded],
    onlySimple: Boolean = false
  ): (Expr, TemplateStructure, Map[Variable, Encoded]) = {
    val (struct, depsByScope) = normalizeStructure(exprOps.freshenLocals(expr), onlySimple = onlySimple)
    val deps = depsByScope.toMap

    lazy val isNormalForm: Boolean = {
      def extractBody(e: Expr): (Seq[ValDef], Expr) = e match {
        case Lambda(args, body) =>
          val (nextArgs, nextBody) = extractBody(body)
          (args ++ nextArgs, nextBody)
        case _ => (Seq.empty, e)
      }

      val (params, app) = extractBody(struct)
      !app.getType.isInstanceOf[FunctionType] && (ApplicationExtractor(app) exists {
        case (caller: Variable, args) => (params.map(_.toVariable) == args) && (deps.get(caller) match {
          case Some(_: Application | _: FunctionInvocation | _: Variable | _: ADTSelector) => true
          case _ => false
        })
        case _ => false
      })
    }

    type DepClauses = (
      Map[Variable, Encoded],
      Map[Variable, Encoded],
      Map[Variable, Set[Variable]],
      Clauses,
      Calls,
      Apps,
      Matchers,
      Equalities,
      Seq[LambdaTemplate],
      Seq[QuantificationTemplate],
      Pointers
    )

    val (depSubst, depContents) =
      depsByScope.foldLeft(substMap, TemplateContents.empty(pathVar -> substMap(pathVar), Seq())) {
        case ((depSubst, contents), (v, expr)) =>
          if (!isSimple(expr)) {
            val normalExpr = if (!isNormalForm) simplifyHOFunctions(expr) else expr
            val (e, cls) = mkExprClauses(pathVar, normalExpr, depSubst)

            // setup the full encoding substMap
            val (conds, exprs, chooses, tree, equals, lmbds, quants) = cls.proj
            val clauseSubst: Map[Variable, Encoded] = depSubst ++ conds ++ exprs ++ chooses ++
              lmbds.map(_.ids) ++ quants.flatMap(_.mapping) ++ equals.flatMap(_._2.map(_.symbols))

            val (eCalls, eApps, eMatchers, ePointers) = Template.extractCalls(e, clauseSubst)
            val (clsClauses, clsCalls, clsApps, clsMatchers, clsPointers, _) =
              Template.encode(pathVar -> substMap(pathVar), Seq.empty, cls, clauseSubst)

            (depSubst + (v -> mkEncoder(clauseSubst)(e)), contents merge (
              conds,
              exprs,
              chooses,
              tree,
              clsClauses,
              clsCalls merge Map(substMap(pathVar) -> eCalls),
              clsApps merge Map(substMap(pathVar) -> eApps),
              clsMatchers merge Map(substMap(pathVar) -> eMatchers),
              equals,
              lmbds,
              quants,
              clsPointers ++ ePointers
            ))
          } else {
            val encoder = mkEncoder(depSubst) _
            val ePointers = Template.lambdaPointers(encoder)(expr)
            (depSubst + (v -> encoder(expr)), contents.copy(pointers = contents.pointers ++ ePointers))
          }
      }

    val sortedDeps = exprOps.variablesOf(struct).map(v => v -> deps(v)).toSeq.sortBy(_._1.id.uniqueName)
    val dependencies = sortedDeps.map(p => depSubst(p._1))
    val structure = new TemplateStructure(struct, dependencies, depContents)

    val res = if (isNormalForm) expr else struct
    (res, structure, depSubst)
  }

  protected def mkExprClauses(
    pathVar: Variable,
    expr: Expr,
    substMap: Map[Variable, Encoded],
    polarity: Option[Boolean] = None
  ): (Expr, TemplateClauses) = {
    var condVars = Map[Variable, Encoded]()
    var condTree = Map[Variable, Set[Variable]](pathVar -> Set.empty).withDefaultValue(Set.empty)
    def storeCond(pathVar: Variable, id: Variable): Unit = {
      condVars += id -> encodeSymbol(id)
      condTree += pathVar -> (condTree(pathVar) + id)
    }

    @inline def encodedCond(id: Variable): Encoded = substMap.getOrElse(id, condVars(id))

    var exprVars = Map[Variable, Encoded]()
    @inline def storeExpr(id: Variable): Unit = exprVars += id -> encodeSymbol(id)

    var chooseVars = Map[Variable, Encoded]()
    @inline def storeChoose(id: Variable): Unit = chooseVars += id -> encodeSymbol(id)

    // Represents clauses of the form:
    //    id => expr && ... && expr
    var guardedExprs = Map[Variable, Seq[Expr]]()
    def storeGuarded(guardVar: Variable, expr: Expr): Unit = {
      assert(expr.getType == BooleanType, expr.asString + " is not of type Boolean. " + explainTyping(expr))

      val prev = guardedExprs.getOrElse(guardVar, Nil)
      guardedExprs += guardVar -> (expr +: prev)
    }

    // Represents equations (simple formulas)
    var equations = Seq[Expr]()
    @inline def iff(e1: Expr, e2: Expr): Unit = equations :+= Equals(e1, e2)

    var lambdas = Seq[LambdaTemplate]()
    @inline def registerLambda(lambda: LambdaTemplate): Unit = lambdas :+= lambda

    var quantifications = Seq[QuantificationTemplate]()
    @inline def registerQuantification(quantification: QuantificationTemplate): Unit =
      quantifications :+= quantification

    var equalities = Map[Encoded, Set[Equality]]()
    @inline def storeEquality(guardVar: Variable, e1: Expr, e2: Expr): Unit = {
      val b = encodedCond(guardVar)
      val prev: Set[Equality] = equalities.getOrElse(b, Set.empty)
      val encoder: Expr => Encoded = mkEncoder(localSubst)
      equalities += b -> (prev + Equality(bestRealType(e1.getType), encoder(e1), encoder(e2)))
    }

    @inline def localSubst: Map[Variable, Encoded] =
      substMap ++ condVars ++ exprVars ++ chooseVars ++ lambdas.map(_.ids)

    def rec(pathVar: Variable, expr: Expr, pol: Option[Boolean]): Expr = expr match {
      case a @ Assume(cond, body) =>
        val e = rec(pathVar, cond, Some(true))
        storeGuarded(pathVar, e)
        rec(pathVar, body, pol)

      case c @ Choose(res, pred) =>
        val newExpr = res.toVariable.freshen
        storeChoose(newExpr)

        val p = rec(pathVar, exprOps.replace(Map(res.toVariable -> newExpr), pred), Some(true))
        storeGuarded(pathVar, p)
        newExpr

      case l @ Let(i, e: Lambda, b) =>
        val re = rec(pathVar, e, None) // guaranteed variable!
        val rb = rec(pathVar, exprOps.replace(Map(i.toVariable -> re), b), pol)
        rb

      case l @ Let(i, e, b) =>
        val newExpr : Variable = Variable.fresh("lt", i.getType, true)
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
            val newExpr: Variable = Variable.fresh("e", BooleanType, true)
            storeExpr(newExpr)

            def recAnd(pathVar: Variable, partitions: Seq[Expr]): Unit = partitions match {
              case x :: Nil =>
                storeGuarded(pathVar, Equals(newExpr, rec(pathVar, x, pol)))

              case x :: xs =>
                val newRes: Variable = Variable.fresh("res", BooleanType, true)
                storeExpr(newRes)

                val xrec = rec(pathVar, x, pol)
                storeGuarded(pathVar, Equals(newRes, xrec))

                val newBool: Variable = Variable.fresh("b", BooleanType, true)
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
            val newExpr: Variable = Variable.fresh("e", BooleanType, true)
            storeExpr(newExpr)

            def recOr(pathVar: Variable, partitions: Seq[Expr]): Unit = partitions match {
              case x :: Nil =>
                storeGuarded(pathVar, Equals(newExpr, rec(pathVar, x, None)))

              case x :: xs =>
                val newRes: Variable = Variable.fresh("res", BooleanType, true)
                storeExpr(newRes)

                val xrec = rec(pathVar, x, None)
                storeGuarded(pathVar, Equals(newRes, xrec))

                val newBool: Variable = Variable.fresh("b", BooleanType, true)
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
          val newBool1 : Variable = Variable.fresh("b", BooleanType, true)
          val newBool2 : Variable = Variable.fresh("b", BooleanType, true)
          val newExpr  : Variable = Variable.fresh("e", i.getType, true)
          val condVar  : Variable = Variable.fresh("c", BooleanType, true)

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

          if (conjArgs.isEmpty) {
            conj
          } else {
            val forall = Forall(conjArgs, conj)
            val (optVar, template) = QuantificationTemplate(pathVar -> encodedCond(pathVar), pol, forall, localSubst)
            registerQuantification(template)
            optVar.getOrElse(BooleanLiteral(true))
          }
        }

        andJoin(conjunctQs)

      case Equals(e1, e2) if unrollEquality(e1.getType) =>
        val (v, _) = equalitySymbol(bestRealType(e1.getType))
        val re1 = rec(pathVar, e1, pol)
        val re2 = rec(pathVar, e2, pol)
        storeEquality(pathVar, re1, re2)
        Application(v, Seq(re1, re2))

      case Operator(as, r) => r(as.map(a => rec(pathVar, a, None)))
    }

    val p = rec(pathVar, expr, polarity)
    (p, (condVars, exprVars, chooseVars, condTree, guardedExprs, equations, equalities, lambdas, quantifications))
  }
}
