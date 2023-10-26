/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import scala.collection.mutable.{Map => MutableMap}

trait TemplateGenerator { self: Templates =>
  import context._
  import program._
  import program.trees._
  import program.symbols._

  protected type TemplateClauses = (
    Map[Variable, Encoded],
    Map[Variable, Encoded],
    Map[Variable, Set[Variable]],
    Map[Variable, Seq[Expr]],
    Seq[Expr],
    Types,
    Equalities,
    Seq[LambdaTemplate],
    Seq[QuantificationTemplate]
  )

  protected def emptyClauses: TemplateClauses =
    (Map.empty, Map.empty, Map.empty, Map.empty, Seq.empty, Map.empty, Map.empty, Seq.empty, Seq.empty)

  protected implicit class ClausesWrapper(clauses: TemplateClauses) {
    def ++(that: TemplateClauses): TemplateClauses = {
      val (thisConds, thisExprs, thisTree, thisGuarded, thisEqs, thisTps, thisEqualities, thisLambdas, thisQuants) = clauses
      val (thatConds, thatExprs, thatTree, thatGuarded, thatEqs, thatTps, thatEqualities, thatLambdas, thatQuants) = that

      (thisConds ++ thatConds, thisExprs ++ thatExprs, thisTree merge thatTree,
        thisGuarded merge thatGuarded, thisEqs ++ thatEqs, thisTps merge thatTps,
        thisEqualities merge thatEqualities, thisLambdas ++ thatLambdas, thisQuants ++ thatQuants)
    }

    def +(pair: (Variable, Expr)): TemplateClauses = {
      val (thisConds, thisExprs, thisTree, thisGuarded, thisEqs, thisTps, thisEqualities, thisLambdas, thisQuants) = clauses
      (thisConds, thisExprs, thisTree, thisGuarded merge pair, thisEqs, thisTps, thisEqualities, thisLambdas, thisQuants)
    }

    def proj: (
      Map[Variable, Encoded],
      Map[Variable, Encoded],
      Map[Variable, Set[Variable]],
      Types,
      Equalities,
      Seq[LambdaTemplate],
      Seq[QuantificationTemplate]
    ) = {
      val (thisConds, thisExprs, thisTree, _, _, thisTypes, thisEqualities, thisLambdas, thisQuants) = clauses
      (thisConds, thisExprs, thisTree, thisTypes, thisEqualities, thisLambdas, thisQuants)
    }
  }

  private def isSimple(expr: Expr): Boolean = {
    exprOps.isSimple(expr) && !exprOps.exists {
      case Equals(e1, e2) => unrollEquality(e1.getType)
      case _ => false
    } (expr)
  }

  def mkClauses(pathVar: Variable, expr: Expr, substMap: Map[Variable, Encoded], polarity: Option[Boolean] = None): TemplateClauses = {
    val (p, tmplClauses) = mkExprClauses(pathVar, expr, substMap, polarity)
    tmplClauses + (pathVar -> p)
  }

  def mkClauses(pathVar: Variable, tpe: Type, expr: Expr, substMap: Map[Variable, Encoded])
               (implicit generator: TypingGenerator): TemplateClauses = {
    val (p, tmplClauses) = mkTypeClauses(pathVar, tpe, expr, substMap)
    tmplClauses + (pathVar -> p)
  }

  def mergeCalls(pathVar: Variable, condVar: Variable, substMap: Map[Variable, Encoded],
                thenClauses: TemplateClauses, elseClauses: TemplateClauses): TemplateClauses = {
    val builder = new Builder(pathVar, substMap)
    builder ++= thenClauses
    builder ++= elseClauses

    // Clear all guardedExprs in builder since we're going to transform them by merging calls.
    // The transformed guardedExprs will be added to builder at the end of the function.
    builder.guardedExprs = Map.empty

    def collectCalls(expr: Expr): Set[FunctionInvocation] =
      exprOps.collect { case fi: FunctionInvocation => Set(fi) case _ => Set.empty[FunctionInvocation] }(expr)
    def countCalls(expr: Expr): Int =
      exprOps.count { case fi: FunctionInvocation => 1 case _ => 0}(expr)
    def replaceCall(call: FunctionInvocation, newExpr: Expr)(e: Expr): Expr =
      exprOps.replace(Map(call -> newExpr), e)

    def getCalls(guardedExprs: Map[Variable, Seq[Expr]]): Map[TypedFunDef, Seq[(FunctionInvocation, Set[Variable])]] =
      (for { (b, es) <- guardedExprs.toSeq; e <- es; fi <- collectCalls(e) } yield (b -> fi))
      .groupBy(_._2)
      .view.mapValues(_.map(_._1).toSet)
      .toSeq
      .groupBy(_._1.tfd)
      .view.mapValues(_.toList.distinct.sortBy(p => countCalls(p._1)))  // place inner calls first
      .toMap

    var thenGuarded = thenClauses._4
    var elseGuarded = elseClauses._4

    val thenCalls = getCalls(thenGuarded)
    val elseCalls = getCalls(elseGuarded)

    // We sort common function calls in order to merge nested calls first.
    var toMerge: Seq[((FunctionInvocation, Set[Variable]), (FunctionInvocation, Set[Variable]))] =
      (thenCalls.keySet & elseCalls.keySet)
        .flatMap(tfd => thenCalls(tfd) zip elseCalls(tfd))
        .toSeq
        .sortBy(p => countCalls(p._1._1) + countCalls(p._2._1))

    while (toMerge.nonEmpty) {
      val ((thenCall, thenBlockers), (elseCall, elseBlockers)) = toMerge.head
      toMerge = toMerge.tail

      val newExpr: Variable = Variable.fresh("call", thenCall.tfd.getType, true)
      builder.storeExpr(newExpr)

      val replaceThen = replaceCall(thenCall, newExpr) _
      val replaceElse = replaceCall(elseCall, newExpr) _

      thenGuarded = thenGuarded.view.mapValues(_.map(replaceThen)).toMap
      elseGuarded = elseGuarded.view.mapValues(_.map(replaceElse)).toMap
      toMerge = toMerge.map(p => (
        (replaceThen(p._1._1).asInstanceOf[FunctionInvocation], p._1._2),
        (replaceElse(p._2._1).asInstanceOf[FunctionInvocation], p._2._2)
      ))

      val newBlocker: Variable = Variable.fresh("bm", BooleanType(), true)
      builder.storeConds(thenBlockers ++ elseBlockers, newBlocker)
      builder.iff(orJoin((thenBlockers ++ elseBlockers).toSeq), newBlocker)

      val newArgs = (thenCall.args zip elseCall.args).map { case (thenArg, elseArg) =>
        val (newArg, argClauses) = mkExprClauses(newBlocker, ifExpr(condVar, thenArg, elseArg), builder.localSubst)
        builder ++= argClauses
        newArg
      }

      val newCall = thenCall.tfd.applied(newArgs).copiedFrom(thenCall)
      builder.storeGuarded(newBlocker, Equals(newExpr, newCall))
    }

    for ((b, es) <- thenGuarded; e <- es) builder.storeGuarded(b, e)
    for ((b, es) <- elseGuarded; e <- es) builder.storeGuarded(b, e)
    builder.result
  }

  protected def mkExprStructure(
    pathVar: Variable,
    expr: Expr,
    substMap: Map[Variable, Encoded],
    onlySimple: Boolean = false
  ): (Expr, TemplateStructure, Map[Variable, Encoded]) = {
    val (struct, depsByScope) = normalizeStructure(expr)
    val deps = depsByScope.map { case (v, e, _) => v -> e }.toMap

    val (depSubst, depContents) =
      depsByScope.foldLeft(substMap, TemplateContents.empty(pathVar -> substMap(pathVar), Seq())) {
        case ((depSubst, contents), (v, expr, conditions)) =>
          if (isSimple(expr)) {
            // Note that we can ignore conditions in this case as the underlying
            // solver is able to find satisfying assignments for all simple terms
            val encoder = mkEncoder(depSubst) _
            val ePointers = Template.lambdaPointers(encoder)(expr)
            (depSubst + (v -> encoder(expr)), contents.copy(pointers = contents.pointers ++ ePointers))
          } else if (!isSimple(expr) && conditions.isEmpty) {
            // We optimize for the case where conditions is empty as the quantifier
            // instantiation procedure relies on path condition variables staying the
            // same whenever possible.
            val (e, cls) = mkExprClauses(pathVar, expr, depSubst)

            // setup the full encoding substMap
            val (conds, exprs, tree, types, equals, lmbds, quants) = cls.proj
            val clauseSubst: Map[Variable, Encoded] = depSubst ++ conds ++ exprs ++
              lmbds.map(_.ids) ++ quants.flatMap(_.mapping) ++ equals.flatMap(_._2.map(_.symbols))

            val (eCalls, eApps, eMatchers, ePointers) = Template.extractCalls(e, clauseSubst)
            val (clsClauses, clsCalls, clsApps, clsMatchers, clsPointers, _) =
              Template.encode(pathVar -> substMap(pathVar), Seq.empty, cls, clauseSubst)

            (depSubst + (v -> mkEncoder(clauseSubst)(e)), contents merge (
              conds, exprs, tree, clsClauses, types,
              clsCalls merge Map(substMap(pathVar) -> eCalls),
              clsApps merge Map(substMap(pathVar) -> eApps),
              clsMatchers merge Map(substMap(pathVar) -> eMatchers),
              equals, lmbds, quants, clsPointers ++ ePointers
            ))
          } else {
            val condVar = Variable.fresh("p", BooleanType())
            val exprVar = Variable.fresh("r", v.getType)

            val localSubst = depSubst + (condVar -> encodeSymbol(condVar)) + (exprVar -> encodeSymbol(exprVar))
            val cls = mkClauses(pathVar, Equals(condVar, andJoin(conditions)), localSubst) ++
              mkClauses(condVar, Equals(exprVar, expr), localSubst)

            // setup the full encoding substMap
            val (conds, exprs, tree, types, equals, lmbds, quants) = cls.proj
            val clauseSubst: Map[Variable, Encoded] = localSubst ++ conds ++ exprs ++
              lmbds.map(_.ids) ++ quants.flatMap(_.mapping) ++ equals.flatMap(_._2.map(_.symbols))

            val (clsClauses, clsCalls, clsApps, clsMatchers, clsPointers, _) =
              Template.encode(pathVar -> substMap(pathVar), Seq.empty, cls, clauseSubst)

            (depSubst + (v -> localSubst(exprVar)), contents merge (
              conds + (condVar -> localSubst(condVar)),
              exprs + (exprVar -> localSubst(exprVar)),
              tree merge Map(pathVar -> Set(condVar)),
              clsClauses, types, clsCalls, clsApps, clsMatchers, equals, lmbds, quants, clsPointers
            ))
          }
      }

    val sortedDeps = exprOps.variablesOf(struct).map(v => v -> deps(v)).toSeq.sortBy(_._1.id)
    val dependencies = sortedDeps.map(p => depSubst(p._1))
    val structure = new TemplateStructure(struct, dependencies, depContents)

    val freshSubst = exprOps.variablesOf(struct).map(v => v -> v.freshen).toMap
    val freshDeps = depSubst.map { case (v, e) => freshSubst.getOrElse(v, v) -> e }
    (exprOps.replaceFromSymbols(freshSubst, struct), structure, freshDeps)
  }

  final private class Builder(pathVar: Variable, substMap: Map[Variable, Encoded]) {
    var condVars = Map[Variable, Encoded]()
    var condTree = Map[Variable, Set[Variable]](pathVar -> Set.empty)
    def storeCond(pathVar: Variable, id: Variable): Unit = {
      condVars += id -> encodeSymbol(id)
      condTree += pathVar -> (condTree.getOrElse(pathVar, Set.empty) + id)
    }

    def storeConds(pathVars: Set[Variable], id: Variable): Unit = {
      condVars += id -> encodeSymbol(id)
      for (pathVar <- pathVars) {
        condTree += pathVar -> (condTree.getOrElse(pathVar, Set.empty) + id)
      }
    }

    @inline def encodedCond(id: Variable): Encoded = substMap.getOrElse(id, condVars(id))

    var exprVars = Map[Variable, Encoded]()
    @inline def storeExpr(id: Variable): Unit = exprVars += id -> encodeSymbol(id)

    // Represents clauses of the form:
    //    id => expr && ... && expr
    var guardedExprs = Map[Variable, Seq[Expr]]()
    def storeGuarded(guardVar: Variable, expr: Expr): Unit = {
      assert(expr.getType == BooleanType(), expr.asString + " is not of type Boolean. " + explainTyping(expr))

      val prev = guardedExprs.getOrElse(guardVar, Nil)
      guardedExprs += guardVar -> (expr +: prev)
    }

    var types = Map[Encoded, Set[Typing]]()
    def storeType(pathVar: Variable, tpe: Type, arg: Expr)(implicit generator: TypingGenerator): Expr = {
      val b = encodedCond(pathVar)
      val encoder = mkEncoder(localSubst) _
      val closures = typeOps.variablesOf(tpe).toSeq.sortBy(_.id).map(encoder).map(Left(_))
      val (result, typing) = generator match {
        case FreeGenerator | ContractGenerator=>
          val typeCall: Variable = Variable.fresh("tp", BooleanType(), true)
          storeExpr(typeCall)

          (typeCall, Typing(tpe, encoder(arg), Constraint(exprVars(typeCall), closures, generator == FreeGenerator)))

        case CaptureGenerator(container, containerType) =>
          // @nv: note that we only store the non-dependent type here as we don't need
          //      to consider dependent types when looking at captures
          (BooleanLiteral(true), Typing(tpe.getType, encoder(arg), Capture(container, containerType)))
      }

      types += b -> (types.getOrElse(b, Set.empty) + typing)
      result
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
      equalities += b -> (prev + Equality(e1.getType, encoder(e1), encoder(e2)))
    }

    @inline def localSubst: Map[Variable, Encoded] =
      substMap ++ condVars ++ exprVars ++ lambdas.map(_.ids)

    def result: TemplateClauses =
      (condVars, exprVars, condTree, guardedExprs, equations, types, equalities, lambdas, quantifications)

    def ++=(that: TemplateClauses): this.type = {
      val (conds, exprs, tree, guarded, eqs, tpes, equls, lmbds, quants) = that
      condVars ++= conds
      exprVars ++= exprs
      condTree = condTree merge tree
      guardedExprs = guardedExprs merge guarded
      equations ++= eqs
      types = types merge tpes
      equalities ++= equls
      lambdas ++= lmbds
      quantifications ++= quants
      this
    }
  }

  protected def mkExprClauses(
    pathVar: Variable,
    expr: Expr,
    substMap: Map[Variable, Encoded],
    polarity: Option[Boolean] = None
  ): (Expr, TemplateClauses) = {
    val builder = new Builder(pathVar, substMap)
    import builder._

    def rec(pathVar: Variable, expr: Expr, pol: Option[Boolean]): Expr = expr match {
      case a @ Assume(cond, body) =>
        val e = rec(pathVar, cond, Some(true))
        storeGuarded(pathVar, e)
        rec(pathVar, body, pol)

      case c @ Choose(res, pred) =>
        val newExpr = res.toVariable.freshen
        storeExpr(newExpr)

        val (tpeExpr, tmplClauses) = mkTypeClauses(pathVar, res.tpe, newExpr, localSubst)(FreeGenerator)
        storeGuarded(pathVar, tpeExpr)
        builder ++= tmplClauses

        val p = rec(pathVar, exprOps.replace(Map(res.toVariable -> newExpr), pred), Some(true))
        storeGuarded(pathVar, p)
        newExpr

      case l @ Let(i, e: Lambda, b) =>
        val re = rec(pathVar, e, None) // guaranteed variable!
        val rb = rec(pathVar, exprOps.replace(Map(i.toVariable -> re), b), pol)
        rb

      case l @ Let(i, e, b) =>
        val newExpr: Variable = Variable.fresh("lt", i.getType, true)
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
            val newExpr: Variable = Variable.fresh("e", BooleanType(), true)
            storeExpr(newExpr)

            def recAnd(pathVar: Variable, partitions: Seq[Expr]): Unit = partitions match {
              case x :: Nil =>
                storeGuarded(pathVar, Equals(newExpr, rec(pathVar, x, pol)))

              case x :: xs =>
                val newRes: Variable = Variable.fresh("res", BooleanType(), true)
                storeExpr(newRes)

                val xrec = rec(pathVar, x, pol)
                storeGuarded(pathVar, Equals(newRes, xrec))

                val newBool: Variable = Variable.fresh("b", BooleanType(), true)
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
            val newExpr: Variable = Variable.fresh("e", BooleanType(), true)
            storeExpr(newExpr)

            def recOr(pathVar: Variable, partitions: Seq[Expr]): Unit = partitions match {
              case x :: Nil =>
                storeGuarded(pathVar, Equals(newExpr, rec(pathVar, x, pol)))

              case x :: xs =>
                val newRes: Variable = Variable.fresh("res", BooleanType(), true)
                storeExpr(newRes)

                val xrec = rec(pathVar, x, None)
                storeGuarded(pathVar, Equals(newRes, xrec))

                val newBool: Variable = Variable.fresh("b", BooleanType(), true)
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
          val newBool1 : Variable = Variable.fresh("b", BooleanType(), true)
          val newBool2 : Variable = Variable.fresh("b", BooleanType(), true)
          val newExpr  : Variable = Variable.fresh("e", i.getType, true)
          val condVar  : Variable = Variable.fresh("c", BooleanType(), true)

          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)
          storeExpr(newExpr)
          storeExpr(condVar)

          val crec = rec(pathVar, cond, None)
          storeGuarded(pathVar, Equals(condVar, crec))
          iff(and(pathVar, condVar), newBool1)
          iff(and(pathVar, not(condVar)), newBool2)

          val (trec, tClauses) = mkExprClauses(newBool1, thenn, localSubst, pol)
          val (erec, eClauses) = mkExprClauses(newBool2, elze, localSubst, pol)
          builder ++=  mergeCalls(pathVar, condVar, localSubst,
                                  tClauses + (newBool1 -> Equals(newExpr, trec)),
                                  eClauses + (newBool2 -> Equals(newExpr, erec)))

          newExpr
        }
      }

      case l: Lambda =>
        val template = LambdaTemplate(pathVar -> encodedCond(pathVar), l, localSubst)
        builder.registerLambda(template)
        template.ids._1

      case f: Forall =>
        val (assumptions, without: Forall) = liftAssumptions(f)

        for (a <- assumptions) {
          rec(pathVar, a, Some(true))
        }

        val TopLevelAnds(conjuncts) = without.body

        val conjunctQs = conjuncts.map { conj =>
          val vars = exprOps.variablesOf(conj)
          val conjArgs = without.params.filter(vd => vars(vd.toVariable) || hasInstance(vd.tpe) != Some(true))

          if (conjArgs.isEmpty) {
            rec(pathVar, conj, pol)
          } else {
            val forall = Forall(conjArgs, conj)
            pol match {
              case Some(p) =>
                val (res, template) = QuantificationTemplate(pathVar -> encodedCond(pathVar), p, forall, localSubst)
                registerQuantification(template)
                res
              case None =>
                val (res, negTemplate) = QuantificationTemplate(pathVar -> encodedCond(pathVar), false, forall, localSubst)

                val inst = Variable.fresh("neg-inst", BooleanType(), true)
                storeExpr(inst)
                iff(inst, res)

                val (_, posTemplate) = QuantificationTemplate(inst -> exprVars(inst), true, forall, localSubst, defer = true)
                registerQuantification(negTemplate)
                registerQuantification(posTemplate)
                res
            }
          }
        }

        andJoin(conjunctQs)

      case Equals(e1, e2) if unrollEquality(e1.getType) =>
        val (v, _) = equalitySymbol(e1.getType)
        val re1 = rec(pathVar, e1, pol)
        val re2 = rec(pathVar, e2, pol)
        storeEquality(pathVar, re1, re2)
        Application(v, Seq(re1, re2))

      case Operator(as, recons) => recons(as.map(a => rec(pathVar, a, None))).copiedFrom(expr)
    }

    val p = rec(pathVar, expr, polarity)
    (p, builder.result)
  }

  /** Generates the clauses and other bookkeeping relevant to a type unfolding template. */
  protected def mkTypeClauses(
    pathVar: Variable,
    tpe: Type,
    expr: Expr,
    substMap: Map[Variable, Encoded]
  )(implicit generator: TypingGenerator): (Expr, TemplateClauses) = {
    val builder = new Builder(pathVar, substMap)
    import builder._

    case class RecursionState(
      recurseAdt: Boolean, // visit adt children/fields
      recurseMap: Boolean, // unroll map definition
      recurseSet: Boolean, // unroll set definition
      recurseBag: Boolean  // unroll bag definition
    )

    def rec(pathVar: Variable, tpe: Type, expr: Expr, state: RecursionState): Expr = tpe match {
      case tpe if !(generator unroll tpe) => BooleanLiteral(true) // nothing to do here!

      case (_: FunctionType | _: PiType) => storeType(pathVar, tpe, expr)

      case tp: TypeParameter if generator == FreeGenerator => typesManager.storeTypeParameter(tp)

      case RefinementType(vd, pred) =>
        val newExpr: Variable = Variable.fresh("lt", vd.getType, true)
        storeExpr(newExpr)

        storeGuarded(pathVar, Equals(newExpr, expr))

        val (p, predClauses) = mkExprClauses(pathVar,
          exprOps.replaceFromSymbols(Map(vd -> newExpr), pred), localSubst)
        builder ++= predClauses

        and(rec(pathVar, vd.tpe, expr, state), p)

      case SigmaType(params, to) =>
        val (newExprs, recParams) = params.zipWithIndex.map { case (vd, i) =>
          val newExpr: Variable = Variable.fresh("lt", vd.getType, true)
          storeExpr(newExpr)

          storeGuarded(pathVar, Equals(newExpr, TupleSelect(expr, i + 1)))
          (newExpr, rec(pathVar, vd.tpe, newExpr, state))
        }.unzip

        val recTo = rec(pathVar,
          typeOps.replaceFromSymbols((params zip newExprs).toMap, to),
          TupleSelect(expr, params.size + 1), state)

        andJoin(recParams :+ recTo)

      case adt: ADTType =>
        val sort = adt.getSort

        and(
          sort.invariant
            .filter(_ => generator == FreeGenerator)
            .map(tfd => tfd.applied(Seq(expr)).copiedFrom(tfd))
            .getOrElse(BooleanLiteral(true)),
          if (sort.definition.isInductive && !state.recurseAdt) {
            storeType(pathVar, tpe, expr)
          } else {
            val newExpr = Variable.fresh("e", BooleanType(), true)
            storeExpr(newExpr)

            val stored = for (tcons <- sort.constructors) yield {
              if (tcons.fields.exists(vd => generator unroll vd.tpe)) {
                val newBool: Variable = Variable.fresh("b", BooleanType(), true)
                storeCond(pathVar, newBool)

                val recProp = andJoin(for (vd <- tcons.fields) yield {
                  rec(newBool, vd.tpe, ADTSelector(expr, vd.id), state.copy(recurseAdt = false))
                })

                iff(and(pathVar, isCons(expr, tcons.id)), newBool)
                storeGuarded(newBool, Equals(newExpr, recProp))
                true
              } else {
                false
              }
            }

            if (stored.foldLeft(false)(_ || _)) {
              newExpr
            } else {
              BooleanLiteral(true)
            }
          }
        )

      case TupleType(tpes) =>
        andJoin(for ((tpe, idx) <- tpes.zipWithIndex) yield {
          rec(pathVar, tpe, TupleSelect(expr, idx + 1), state)
        })

      case MapType(from, to) =>
        if (!state.recurseMap) {
          storeType(pathVar, tpe, expr)
        } else {
          val newBool1 : Variable = Variable.fresh("mapIsEmpty", BooleanType(), true)
          val newBool2 : Variable = Variable.fresh("mapNonEmpty", BooleanType(), true)
          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)

          val condVar  : Variable = Variable.fresh("condMapEmpty", BooleanType(), true)
          val newExpr = Variable.fresh("mapRes", BooleanType(), true)
          val keyExpr: Variable = Variable.fresh("mapKey", from, true)
          val valueExpr: Variable = Variable.fresh("mapValue", to, true)
          val defaultExpr: Variable = Variable.fresh("mapDefault", to, true)
          val restExpr: Variable = Variable.fresh("mapRest", tpe, true)
          storeExpr(condVar)
          storeExpr(newExpr)
          storeExpr(keyExpr)
          storeExpr(valueExpr)
          storeExpr(defaultExpr)
          storeExpr(restExpr)

          storeGuarded(pathVar, Equals(condVar, Equals(expr, FiniteMap(Seq(), defaultExpr, from, to))))
          iff(and(pathVar, condVar), newBool1)
          iff(and(pathVar, not(condVar)), newBool2)

          storeGuarded(newBool1, newExpr)
          storeGuarded(newBool2, Equals(expr, MapUpdated(restExpr, keyExpr, valueExpr)))
          storeGuarded(newBool2, Equals(newExpr, and(
            rec(newBool2, tpe, restExpr, state.copy(recurseMap = false)),
            rec(newBool2, from, keyExpr, state),
            rec(newBool2, to, valueExpr, state)
          )))

          and(rec(pathVar, to, defaultExpr, state), newExpr)
        }

      case SetType(base) =>
        if (!state.recurseSet) {
          storeType(pathVar, tpe, expr)
        } else {
          val newBool1 : Variable = Variable.fresh("setIsEmpty", BooleanType(), true)
          val newBool2 : Variable = Variable.fresh("setNonEmpty", BooleanType(), true)
          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)

          val condVar  : Variable = Variable.fresh("condSetEmpty", BooleanType(), true)
          val newExpr = Variable.fresh("setRes", BooleanType(), true)
          val elemExpr: Variable = Variable.fresh("setElem", base, true)
          val restExpr: Variable = Variable.fresh("setRest", tpe, true)
          storeExpr(condVar)
          storeExpr(newExpr)
          storeExpr(elemExpr)
          storeExpr(restExpr)

          storeGuarded(pathVar, Equals(condVar, Equals(expr, FiniteSet(Seq(), base))))
          iff(and(pathVar, condVar), newBool1)
          iff(and(pathVar, not(condVar)), newBool2)

          storeGuarded(newBool1, newExpr)
          storeGuarded(newBool2, Equals(expr, SetUnion(FiniteSet(Seq(elemExpr), base), restExpr)))
          storeGuarded(newBool2, Equals(newExpr, and(
            rec(newBool2, tpe, restExpr, state.copy(recurseSet = false)),
            rec(newBool2, base, elemExpr, state)
          )))

          newExpr
        }

      case BagType(base) =>
        if (!state.recurseBag) {
          storeType(pathVar, tpe, expr)
        } else {
          val newBool1 : Variable = Variable.fresh("bagIsEmpty", BooleanType(), true)
          val newBool2 : Variable = Variable.fresh("bagNonEmpty", BooleanType(), true)
          storeCond(pathVar, newBool1)
          storeCond(pathVar, newBool2)

          val condVar  : Variable = Variable.fresh("condBagEmpty", BooleanType(), true)
          val newExpr = Variable.fresh("bagRes", BooleanType(), true)
          val elemExpr: Variable = Variable.fresh("bagElem", base, true)
          val multExpr: Variable = Variable.fresh("bagMult", IntegerType(), true)
          val restExpr: Variable = Variable.fresh("bagRest", tpe, true)
          storeExpr(condVar)
          storeExpr(newExpr)
          storeExpr(elemExpr)
          storeExpr(multExpr)
          storeExpr(restExpr)

          storeGuarded(pathVar, Equals(condVar, Equals(expr, FiniteBag(Seq(), base))))
          iff(and(pathVar, condVar), newBool1)
          iff(and(pathVar, not(condVar)), newBool2)

          storeGuarded(newBool1, newExpr)
          storeGuarded(newBool2, Equals(expr, BagUnion(FiniteBag(Seq((elemExpr, multExpr)), base), restExpr)))
          storeGuarded(newBool2, GreaterThan(multExpr, IntegerLiteral(0)))
          storeGuarded(newBool2, Equals(newExpr, and(
            rec(newBool2, tpe, restExpr, state.copy(recurseBag = false)),
            rec(newBool2, base, elemExpr, state),
            rec(newBool2, IntegerType(), multExpr, state)
          )))

          newExpr
        }

      case _ => throw new InternalSolverError(s"Unexpected unrollable: ${tpe.asString}")
    }

    val p = rec(pathVar, tpe, expr, RecursionState(true, true, true, true))
    (p, builder.result)
  }
}
