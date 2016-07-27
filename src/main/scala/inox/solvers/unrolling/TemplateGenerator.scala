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

  val assumePreHolds: Boolean

  private type TemplateClauses = (
    Map[Variable, Encoded],
    Map[Variable, Encoded],
    Map[Variable, Set[Variable]],
    Map[Variable, Seq[Expr]],
    Seq[LambdaTemplate],
    Seq[QuantificationTemplate]
  )

  private def emptyClauses: TemplateClauses = (Map.empty, Map.empty, Map.empty, Map.empty, Seq.empty, Seq.empty)

  private implicit class ClausesWrapper(clauses: TemplateClauses) {
    def ++(that: TemplateClauses): TemplateClauses = {
      val (thisConds, thisExprs, thisTree, thisGuarded, thisLambdas, thisQuants) = clauses
      val (thatConds, thatExprs, thatTree, thatGuarded, thatLambdas, thatQuants) = that

      (thisConds ++ thatConds, thisExprs ++ thatExprs, thisTree merge thatTree,
        thisGuarded merge thatGuarded, thisLambdas ++ thatLambdas, thisQuants ++ thatQuants)
    }
  }

  private val cache: MutableMap[TypedFunDef, FunctionTemplate] = MutableMap.empty

  def mkTemplate(tfd: TypedFunDef): FunctionTemplate = {
    if (cache contains tfd) {
      return cache(tfd)
    }

    // The precondition if it exists.
    val prec : Option[Expr] = tfd.precondition.map(p => simplifyHOFunctions(matchToIfThenElse(p)))

    val newBody : Option[Expr] = tfd.body.map(b => matchToIfThenElse(b))
    val lambdaBody : Option[Expr] = newBody.map(b => simplifyHOFunctions(b))

    val funDefArgs: Seq[Variable] = tfd.params.map(_.toVariable)
    val lambdaArguments: Seq[Variable] = lambdaBody.map(lambdaArgs).toSeq.flatten
    val invocation : Expr = tfd.applied(funDefArgs)

    val invocationEqualsBody : Seq[Expr] = lambdaBody match {
      case Some(body) =>
        val bs = liftedEquals(invocation, body, lambdaArguments) :+ Equals(invocation, body)

        if(prec.isDefined) {
          bs.map(Implies(prec.get, _))
        } else {
          bs
        }

      case _ =>
        Seq.empty
    }

    val start : Variable = Variable(FreshIdentifier("start", true), BooleanType)
    val pathVar : (Variable, Encoded) = start -> encodeSymbol(start)

    val allArguments : Seq[Variable] = funDefArgs ++ lambdaArguments
    val arguments : Seq[(Variable, Encoded)] = allArguments.map(id => id -> encodeSymbol(id))

    val substMap : Map[Variable, Encoded] = arguments.toMap + pathVar

    val (bodyConds, bodyExprs, bodyTree, bodyGuarded, bodyLambdas, bodyQuantifications) =
      invocationEqualsBody.foldLeft(emptyClauses)((clsSet, cls) => clsSet ++ mkClauses(start, cls, substMap))

    // Now the postcondition.
    val (condVars, exprVars, condTree, guardedExprs, lambdas, quantifications) = tfd.postcondition match {
      case Some(post) =>
        val newPost : Expr = simplifyHOFunctions(application(matchToIfThenElse(post), Seq(invocation)))

        val postHolds : Expr =
          if(tfd.hasPrecondition) {
            if (assumePreHolds) {
              And(prec.get, newPost)
            } else {
              Implies(prec.get, newPost)
            }
          } else {
            newPost
          }

        val (postConds, postExprs, postTree, postGuarded, postLambdas, postQuantifications) = mkClauses(start, postHolds, substMap)
        (bodyConds ++ postConds, bodyExprs ++ postExprs, bodyTree merge postTree, bodyGuarded merge postGuarded, bodyLambdas ++ postLambdas, bodyQuantifications ++ postQuantifications)

      case None =>
        (bodyConds, bodyExprs, bodyTree, bodyGuarded, bodyLambdas, bodyQuantifications)
    }

    val template = FunctionTemplate(tfd, pathVar, arguments,
      condVars, exprVars, condTree, guardedExprs, lambdas, quantifications)
    cache += tfd -> template
    template
  }

  private def lambdaArgs(expr: Expr): Seq[Variable] = expr match {
    case Lambda(args, body) => args.map(_.id.freshen) ++ lambdaArgs(body)
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

  private def minimalFlattening(inits: Set[Variable], conj: Expr): (Set[Variable], Expr) = {
    var mapping: Map[Expr, Expr] = Map.empty
    var quantified: Set[Variable] = inits
    var quantifierEqualities: Seq[(Expr, Variable)] = Seq.empty

    val newConj = exprOps.postMap {
      case expr if mapping.isDefinedAt(expr) =>
        Some(mapping(expr))

      case expr @ QuantificationMatcher(c, args) =>
        val isMatcher = args.exists { case v: Variable => quantified(v) case _ => false }
        val isRelevant = (exprOps.variablesOf(expr) & quantified).nonEmpty
        if (!isMatcher && isRelevant) {
          val newArgs = args.map {
            case arg @ QuantificationMatcher(_, _) if (exprOps.variablesOf(arg) & quantified).nonEmpty =>
              val v = Variable(FreshIdentifier("flat", true), arg.getType)
              quantifierEqualities :+= (arg -> v)
              quantified += v
              v
            case arg => arg
          }

          val newExpr = exprOps.replace((args zip newArgs).toMap, expr)
          mapping += expr -> newExpr
          Some(newExpr)
        } else {
          None
        }

      case _ => None
    } (conj)

    val flatConj = implies(andJoin(quantifierEqualities.map {
      case (arg, id) => Equals(arg, id)
    }), newConj)

    (quantified, flatConj)
  }

  def mkClauses(pathVar: Variable, expr: Expr, substMap: Map[Variable, Encoded]): TemplateClauses = {
    val (p, (condVars, exprVars, condTree, guardedExprs, lambdas, quantifications)) = mkExprClauses(pathVar, expr, substMap)
    val allGuarded = guardedExprs + (pathVar -> (p +: guardedExprs.getOrElse(pathVar, Seq.empty)))
    (condVars, exprVars, condTree, allGuarded, lambdas, quantifications)
  }

  private def mkExprClauses(pathVar: Variable, expr: Expr, substMap: Map[Variable, Encoded]): (Expr, TemplateClauses) = {

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

    def iff(e1: Expr, e2: Expr): Unit = storeGuarded(pathVar, Equals(e1, e2))

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

    def rec(pathVar: Variable, expr: Expr): Expr = {
      expr match {
        case a @ Assert(cond, err, body) =>
          rec(pathVar, IfExpr(cond, body, Error(body.getType, err getOrElse "assertion failed")))

        case e @ Ensuring(_, _) =>
          rec(pathVar, e.toAssert)

        case l @ Let(i, e: Lambda, b) =>
          val re = rec(pathVar, e) // guaranteed variable!
          val rb = rec(pathVar, exprOps.replace(Map(i.toVariable -> re), b))
          rb

        case l @ Let(i, e, b) =>
          val newExpr : Variable = Variable(FreshIdentifier("lt", true), i.getType)
          storeExpr(newExpr)
          val re = rec(pathVar, e)
          storeGuarded(pathVar, Equals(newExpr, re))
          val rb = rec(pathVar, exprOps.replace(Map(i.toVariable -> newExpr), b))
          rb

        case m : MatchExpr => sys.error("'MatchExpr's should have been eliminated before generating templates.")

        case i @ Implies(lhs, rhs) =>
          if (!exprOps.isSimple(i)) {
            rec(pathVar, Or(Not(lhs), rhs))
          } else {
            implies(rec(pathVar, lhs), rec(pathVar, rhs))
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
                  storeGuarded(pathVar, Equals(newExpr, rec(pathVar, x)))

                case x :: xs =>
                  val newBool: Variable = Variable(FreshIdentifier("b", true), BooleanType)
                  storeCond(pathVar, newBool)

                  val xrec = rec(pathVar, x)
                  iff(and(pathVar, xrec), newBool)
                  iff(and(pathVar, not(xrec)), not(newExpr))

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
                  storeGuarded(pathVar, Equals(newExpr, rec(pathVar, x)))

                case x :: xs =>
                  val newBool: Variable = Variable(FreshIdentifier("b", true), BooleanType)
                  storeCond(pathVar, newBool)

                  val xrec = rec(pathVar, x)
                  iff(and(pathVar, xrec), newExpr)
                  iff(and(pathVar, not(xrec)), newBool)

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

            storeCond(pathVar, newBool1)
            storeCond(pathVar, newBool2)

            storeExpr(newExpr)

            val crec = rec(pathVar, cond)
            val trec = rec(newBool1, thenn)
            val erec = rec(newBool2, elze)

            iff(and(pathVar, cond), newBool1)
            iff(and(pathVar, not(cond)), newBool2)

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
          val (lambdaConds, lambdaExprs, lambdaTree, lambdaGuarded, lambdaTemplates, lambdaQuants) =
            clauses.foldLeft(emptyClauses)((clsSet, cls) => clsSet ++ mkClauses(pathVar, cls, clauseSubst))

          val ids: (Variable, Encoded) = lid -> storeLambda(lid)

          val (struct, deps) = normalizeStructure(l)

          val (dependencies, (depConds, depExprs, depTree, depGuarded, depLambdas, depQuants)) =
            deps.foldLeft[(Seq[Encoded], TemplateClauses)](Seq.empty -> emptyClauses) {
              case ((dependencies, clsSet), (id, expr)) =>
                if (!exprOps.isSimple(expr)) {
                  val encoded = encodeSymbol(id)
                  val (e, cls @ (_, _, _, _, lmbds, quants)) = mkExprClauses(pathVar, expr, localSubst)
                  val clauseSubst = localSubst ++ lmbds.map(_.ids) ++ quants.map(_.qs)
                  (dependencies :+ encodeExpr(clauseSubst)(e), clsSet ++ cls)
                } else {
                  (dependencies :+ encodeExpr(localSubst)(expr), clsSet)
                }
            }

          val (depClauses, depCalls, depApps, depMatchers, _) = Template.encode(
            pathVar -> encodedCond(pathVar), Seq.empty,
            depConds, depExprs, depGuarded, depLambdas, depQuants, localSubst)

          val depClosures: Seq[Encoded] = {
            val vars = exprOps.variablesOf(l)
            var cls: Seq[Variable] = Seq.empty
            exprOps.preTraversal { case v: Variable if vars(v) => cls :+= v case _ => } (l)
            cls.distinct.map(localSubst)
          }

          val structure = new LambdaStructure(
            struct, dependencies, pathVar -> encodedCond(pathVar), depClosures,
            depConds, depExprs, depTree, depClauses, depCalls, depApps, depLambdas, depMatchers, depQuants)

          val template = LambdaTemplate(ids, pathVar -> encodedCond(pathVar),
            idArgs zip trArgs, lambdaConds, lambdaExprs, lambdaTree,
            lambdaGuarded, lambdaTemplates, lambdaQuants, structure, localSubst, l)
          registerLambda(template)
          lid

        case f @ Forall(args, body) =>
          val TopLevelAnds(conjuncts) = body

          val conjunctQs = conjuncts.map { conjunct =>
            val vars = exprOps.variablesOf(conjunct)
            val inits = args.map(_.toVariable).filter(vars).toSet
            val (quantifiers, flatConj) = minimalFlattening(inits, conjunct)

            val idQuantifiers : Seq[Variable] = quantifiers.toSeq
            val trQuantifiers : Seq[Encoded] = idQuantifiers.map(encodeSymbol)

            val q: Variable = Variable(FreshIdentifier("q", true), BooleanType)
            val q2: Variable = Variable(FreshIdentifier("qo", true), BooleanType)
            val inst: Variable = Variable(FreshIdentifier("inst", true), BooleanType)
            val guard: Variable = Variable(FreshIdentifier("guard", true), BooleanType)

            val clause = Equals(inst, Implies(guard, flatConj))

            val qs: (Variable, Encoded) = q -> encodeSymbol(q)
            val localSubst: Map[Variable, Encoded] = substMap ++ condVars ++ exprVars ++ lambdaVars
            val clauseSubst: Map[Variable, Encoded] = localSubst ++ (idQuantifiers zip trQuantifiers)
            val (p, (qConds, qExprs, qTree, qGuarded, qTemplates, qQuants)) = mkExprClauses(pathVar, flatConj, clauseSubst)
            assert(qQuants.isEmpty, "Unhandled nested quantification in "+clause)

            val allGuarded = qGuarded + (pathVar -> (Seq(
              Equals(inst, Implies(guard, p)),
              Equals(q, And(q2, inst))
            ) ++ qGuarded.getOrElse(pathVar, Seq.empty)))

            val dependencies: Map[Variable, Encoded] = vars.filterNot(quantifiers).map(id => id -> localSubst(id)).toMap
            val template = QuantificationTemplate(pathVar -> encodedCond(pathVar),
              qs, q2, inst, guard, idQuantifiers zip trQuantifiers, qConds, qExprs, qTree, allGuarded, qTemplates, localSubst,
              dependencies, Forall(quantifiers.toSeq.sortBy(_.id.uniqueName).map(_.toVal), flatConj))
            registerQuantification(template)
            q
          }

          andJoin(conjunctQs)

        case Operator(as, r) => r(as.map(a => rec(pathVar, a)))
      }
    }

    val p = rec(pathVar, expr)
    (p, (condVars, exprVars, condTree, guardedExprs, lambdas, quantifications))
  }

}
