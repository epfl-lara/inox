/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import scala.collection.mutable.{Map => MutableMap}

trait TemplateGenerator { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

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

  /** The interpretation of the uninterpreted function `id` at `tps` in the model that the solver
    * operates under (see [[AbstractUnrollingSolver.partialModel]]), if the model interprets it. */
  def interpretation(id: Identifier, tps: Seq[Type]): Option[Lambda]

  /** The free functions that stand for the uninterpreted functions at their type arguments, whose
    * applications are the uninterpreted calls. They are shared by all templates, and their models are
    * those of the uninterpreted functions. */
  private[unrolling] val uninterpretedFunctions: MutableMap[(Identifier, Seq[Type]), (Variable, Encoded)] = MutableMap.empty
  private[unrolling] val uninterpretedSubst: MutableMap[Variable, Encoded] = MutableMap.empty

  /** The free functions of the uninterpreted functions that the model interprets, whose applications
    * are calls that unfold the interpretation, as calls of the functions of the program unfold their
    * bodies (see [[FunctionTemplates]]). Their interpretations may then be recursive. */
  private[unrolling] val interpretedFunctions: MutableMap[Variable, Interpreted] = MutableMap.empty

  /** The types of the uninterpreted functions, whose free functions only have their erased types,
    * so that their models are extracted within their codomains. */
  private[unrolling] val uninterpretedTypes: MutableMap[(Identifier, Seq[Type]), Type] = MutableMap.empty

  private def uninterpretedFunction(uc: UninterpretedCall): Variable =
    uninterpretedFunctions.getOrElseUpdate(uc.id -> uc.tps, {
      uninterpretedTypes(uc.id -> uc.tps) = uc.tpe
      val f = Variable.fresh(uc.id.name, uc.tpe.getType, true)
      val fT = encodeSymbol(f)
      uninterpretedSubst(f) = fT
      if (interpretation(uc.id, uc.tps).isDefined) interpretedFunctions(f) = Interpreted(uc.id, uc.tps)
      (f, fT)
    })._1

  protected def emptyClauses: TemplateClauses =
    (Map.empty, Map.empty, Map.empty, Map.empty, Seq.empty, Map.empty, Map.empty, Seq.empty, Seq.empty)

  extension (clauses: TemplateClauses) {
    def +++(that: TemplateClauses): TemplateClauses = {
      val (thisConds, thisExprs, thisTree, thisGuarded, thisEqs, thisTps, thisEqualities, thisLambdas, thisQuants) = clauses
      val (thatConds, thatExprs, thatTree, thatGuarded, thatEqs, thatTps, thatEqualities, thatLambdas, thatQuants) = that

      (thisConds ++ thatConds, thisExprs ++ thatExprs, thisTree `merge` thatTree,
        thisGuarded `merge` thatGuarded, thisEqs ++ thatEqs, thisTps `merge` thatTps,
        thisEqualities `merge` thatEqualities, thisLambdas ++ thatLambdas, thisQuants ++ thatQuants)
    }

    def +(pair: (Variable, Expr)): TemplateClauses = {
      val (thisConds, thisExprs, thisTree, thisGuarded, thisEqs, thisTps, thisEqualities, thisLambdas, thisQuants) = clauses
      (thisConds, thisExprs, thisTree, thisGuarded `merge` pair, thisEqs, thisTps, thisEqualities, thisLambdas, thisQuants)
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

  // Due to a Scala 3 bug, if we name the following two methods the same, we encounter a strange error.
  // The following open ticket should be related to our problems:
  // https://github.com/lampepfl/dotty/issues/11226
  def mkClauses0(pathVar: Variable, expr: Expr, substMap: Map[Variable, Encoded], polarity: Option[Boolean] = None): TemplateClauses = {
    val (p, tmplClauses) = mkExprClauses(pathVar, expr, substMap, polarity)
    tmplClauses + (pathVar -> p)
  }

  def mkClauses1(pathVar: Variable, tpe: Type, expr: Expr, substMap: Map[Variable, Encoded])
                (using TypingGenerator): TemplateClauses = {
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

      val replaceThen = replaceCall(thenCall, newExpr)
      val replaceElse = replaceCall(elseCall, newExpr)

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

      val newCall = thenCall.tfd.applied(newArgs)
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
            val encoder = mkEncoder(depSubst)
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

            val (eCalls, eApps, eMatchers, eReads, ePointers) = Template.extractCalls(e, clauseSubst)
            val (clsClauses, clsCalls, clsApps, clsMatchers, clsReads, clsPointers, _) =
              Template.encode(pathVar -> substMap(pathVar), Seq.empty, cls, clauseSubst)

            (depSubst + (v -> mkEncoder(clauseSubst)(e)), contents `merge` (
              conds, exprs, tree, clsClauses, types,
              clsCalls `merge` Map(substMap(pathVar) -> eCalls),
              clsApps `merge` Map(substMap(pathVar) -> eApps),
              clsMatchers `merge` Map(substMap(pathVar) -> eMatchers),
              clsReads `merge` Map(substMap(pathVar) -> eReads),
              equals, lmbds, quants, clsPointers ++ ePointers
            ))
          } else {
            val condVar = Variable.fresh("p", BooleanType())
            val exprVar = Variable.fresh("r", v.getType)

            val localSubst = depSubst + (condVar -> encodeSymbol(condVar)) + (exprVar -> encodeSymbol(exprVar))
            val cls: TemplateClauses = mkClauses0(pathVar, Equals(condVar, andJoin(conditions)), localSubst) +++
              mkClauses0(condVar, Equals(exprVar, expr), localSubst)

            // setup the full encoding substMap
            val (conds, exprs, tree, types, equals, lmbds, quants) = cls.proj
            val clauseSubst: Map[Variable, Encoded] = localSubst ++ conds ++ exprs ++
              lmbds.map(_.ids) ++ quants.flatMap(_.mapping) ++ equals.flatMap(_._2.map(_.symbols))

            val (clsClauses, clsCalls, clsApps, clsMatchers, clsReads, clsPointers, _) =
              Template.encode(pathVar -> substMap(pathVar), Seq.empty, cls, clauseSubst)

            (depSubst + (v -> localSubst(exprVar)), contents `merge` (
              conds + (condVar -> localSubst(condVar)),
              exprs + (exprVar -> localSubst(exprVar)),
              tree `merge` Map(pathVar -> Set(condVar)),
              clsClauses, types, clsCalls, clsApps, clsMatchers, clsReads, equals, lmbds, quants, clsPointers
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
    def storeType(pathVar: Variable, tpe: Type, arg: Expr, inDomain: Boolean = false)
                 (using generator: TypingGenerator): Expr = {
      val b = encodedCond(pathVar)
      val encoder = mkEncoder(localSubst)
      val closures = typeOps.variablesOf(tpe).toSeq.sortBy(_.id).map(encoder).map(Left(_))
      val (result, typing) = generator match {
        case FreeGenerator | ContractGenerator=>
          val typeCall: Variable = Variable.fresh("tp", BooleanType(), true)
          storeExpr(typeCall)

          // Function types are unfolded by `registerFunction`, which doesn't use the flag
          val domain = inDomain && !tpe.isInstanceOf[FunctionType | PiType]
          val constraint = Constraint(exprVars(typeCall), closures, generator == FreeGenerator, domain)
          (typeCall, Typing(tpe, encoder(arg), constraint))

        case MembershipGenerator =>
          val typeCall: Variable = Variable.fresh("tp", BooleanType(), true)
          storeExpr(typeCall)

          (typeCall, Typing(tpe, encoder(arg), Membership(exprVars(typeCall), closures)))

        case CaptureGenerator(container, containerType) =>
          // @nv: note that we only store the non-dependent type here as we don't need
          //      to consider dependent types when looking at captures
          (BooleanLiteral(true), Typing(tpe.getType, encoder(arg), Capture(container, containerType)))
      }

      types += b -> (types.getOrElse(b, Set.empty) + typing)
      result
    }

    // Types the reads of a collection whose elements have contracts or ADT invariants (see [[Collection]]).
    // The elements that only need unrolling as free values (e.g. sets, functions or type parameters) aren't typed:
    // their reads may be many (e.g. those of the heap in Stainless) and typing them doesn't help proofs.
    def storeReads(pathVar: Variable, tpe: Type, elemTpe: Type, arg: Expr, inDomain: Boolean)
                  (using generator: TypingGenerator): Expr =
      if (!(generator == FreeGenerator || (generator == ContractGenerator && !inDomain)) ||
          !(ReadUnrolling `unroll` elemTpe)) BooleanLiteral(true)
      else {
        val b = encodedCond(pathVar)
        val encoder = mkEncoder(localSubst)
        val closures = typeOps.variablesOf(tpe).toSeq.sortBy(_.id).map(encoder).map(Left(_))
        val readsCall: Variable = Variable.fresh("tp", BooleanType(), true)
        storeExpr(readsCall)
        val typing = Typing(tpe, encoder(arg), Collection(exprVars(readsCall), closures, generator == FreeGenerator))
        types += b -> (types.getOrElse(b, Set.empty) + typing)
        readsCall
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
      substMap ++ uninterpretedSubst ++ condVars ++ exprVars ++ lambdas.map(_.ids)

    def result: TemplateClauses =
      (condVars, exprVars, condTree, guardedExprs, equations, types, equalities, lambdas, quantifications)

    def ++=(that: TemplateClauses): this.type = {
      val (conds, exprs, tree, guarded, eqs, tpes, equls, lmbds, quants) = that
      condVars ++= conds
      exprVars ++= exprs
      condTree = condTree `merge` tree
      guardedExprs = guardedExprs `merge` guarded
      equations ++= eqs
      types = types `merge` tpes
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
    exprOps.preTraversal {
      case e if unsupportedContainer(e.getType) =>
        throw new Unsupported(s"${e.getType.asString} relies on a custom equality inside a set, bag or map")
      case _ =>
    } (expr)

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

        val (tpeExpr, tmplClauses) = mkTypeClauses(pathVar, res.tpe, newExpr, localSubst)(using FreeGenerator)
        storeGuarded(pathVar, tpeExpr)
        builder ++= tmplClauses

        val p = rec(pathVar, exprOps.replace(Map(res.toVariable -> newExpr), pred), Some(true))
        storeGuarded(pathVar, p)
        newExpr

      case uc @ UninterpretedCall(id, tps, args, tpe) =>
        // An application of the free function that stands for the uninterpreted function, whose
        // result is an arbitrary value of the call's type, or is given by the interpretation of the
        // function once the call is unfolded
        val f = uninterpretedFunction(uc)
        val (fExpr, fClauses) = mkTypeClauses(pathVar, f.tpe, f, localSubst)(using FreeGenerator)
        storeGuarded(pathVar, fExpr)
        builder ++= fClauses

        val recArgs = args.map(rec(pathVar, _, None))
        val app = Application(f, recArgs).copiedFrom(uc)
        // The result type of the function, with its parameters bound to the arguments of the call
        val resTpe = tpe match {
          case PiType(params, to) => typeOps.replaceFromSymbols((params zip recArgs).toMap, to)
          case FunctionType(_, to) => to
          case _ => throw new IllegalArgumentException(s"Uninterpreted call with type $tpe: $uc")
        }
        val newExpr = Variable.fresh("uc", resTpe.getType, true)
        storeExpr(newExpr)
        storeGuarded(pathVar, Equals(newExpr, app))

        // The refinements of the result hold as the predicate of a choose, and the type that they
        // refine is the type of the result
        def refinements(tpe: Type): (Type, Seq[Expr]) = tpe match {
          case RefinementType(vd, pred) =>
            val (base, preds) = refinements(vd.tpe)
            (base, preds :+ exprOps.replaceFromSymbols(Map(vd -> newExpr), pred))
          case _ => (tpe, Seq.empty)
        }
        val (baseTpe, preds) = refinements(resTpe)

        val (tpeExpr, tmplClauses) = mkTypeClauses(pathVar, baseTpe, newExpr, localSubst)(using FreeGenerator)
        storeGuarded(pathVar, tpeExpr)
        builder ++= tmplClauses

        for (pred <- preds) storeGuarded(pathVar, rec(pathVar, pred, Some(true)))
        newExpr

      case Error(tpe, _) =>
        // Errors are never reached, so the path that leads to one is infeasible
        storeGuarded(pathVar, BooleanLiteral(false))
        val newExpr = Variable.fresh("err", tpe, true)
        storeExpr(newExpr)
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

                // Only a conjunction that must hold forces each conjunct to hold. When it must not
                // hold (e.g. under a negation), any conjunct may be the false one, so we cannot
                // propagate the polarity: a universal quantifier inside `x` would otherwise be
                // asserted under `pathVar`. This mirrors the non-last disjuncts in `Or` below.
                val xrec = rec(pathVar, x, pol.filter(identity))
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
        val (assumptions, without: Forall) = liftAssumptions(f): @unchecked

        for (a <- assumptions) {
          rec(pathVar, a, Some(true))
        }

        val TopLevelAnds(conjuncts) = without.body: @unchecked

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

      case Operator(as, r) => r(as.map(a => rec(pathVar, a, None)))
    }

    val p = rec(pathVar, expr, polarity)
    (p, builder.result)
  }

  /** Whether the clauses of `expr` may falsify the path condition they are guarded by,
    * i.e. whether `expr` contains an assumption or a `choose`, or calls a function that
    * (transitively) does, as unrolling the call falsifies the blocker it is registered under. */
  private def mayFalsifyPath(expr: Expr): Boolean = exprOps.exists {
    case fi: FunctionInvocation => callMayFalsifyPath(fi.id)
    case e => containsAssumption(e)
  }(expr)

  private def containsAssumption(e: Expr): Boolean = e match {
    case _: Assume | _: Choose | _: UninterpretedCall | _: Error => true
    case _ => false
  }

  private val callsMayFalsifyPath: MutableMap[Identifier, Boolean] = MutableMap.empty

  private def callMayFalsifyPath(id: Identifier): Boolean = callsMayFalsifyPath.getOrElseUpdate(id,
    (transitiveCallees(id) + id).exists(fid => exprOps.exists(containsAssumption)(getFunction(fid).fullBody)))

  /** Whether checking that a value belongs to `tpe` may falsify the path condition. */
  private def mayFalsifyPath(tpe: Type): Boolean = typeOps.exists {
    case RefinementType(_, pred) => mayFalsifyPath(pred)
    case _ => false
  }(tpe)

  /** Generates the clauses and other bookkeeping relevant to a type unfolding template.
    *
    * `inDomain` is set when the type check is the domain of a quantifier, i.e. when it appears
    * on the left of an implication and `expr` may range over values outside of `tpe`. The check
    * must then be fully constrained, as the solver could otherwise falsify it to weaken the formula.
    * The flag is carried over to the type templates of nested (inductive) types. */
  protected def mkTypeClauses(
    pathVar: Variable,
    tpe: Type,
    expr: Expr,
    substMap: Map[Variable, Encoded],
    inDomain: Boolean = false
  )(using generator: TypingGenerator): (Expr, TemplateClauses) = {
    val builder = new Builder(pathVar, substMap)
    import builder._

    case class RecursionState(
      recurseAdt: Boolean, // visit adt children/fields
      recurseMap: Boolean, // unroll map definition
      recurseSet: Boolean, // unroll set definition
      recurseBag: Boolean  // unroll bag definition
    )

    // Returns a blocker that holds iff both `pathVar` and `cond` hold. The extra blocker is only
    // introduced when `needed` (see `mayFalsifyPath`), as it slows down unrolling: the clauses
    // it guards are only constrained once the solver has established `cond`, which may require
    // unfolding further type templates.
    def guardedBy(pathVar: Variable, cond: Expr, needed: Boolean, name: String): Variable = cond match {
      case BooleanLiteral(true) => pathVar
      case _ if !needed => pathVar
      case _ =>
        val guard: Variable = Variable.fresh(name, BooleanType(), true)
        storeCond(pathVar, guard)
        iff(and(pathVar, cond), guard)
        guard
    }

    // The result of a guarded check is used under `pathVar`, so any call or application it contains
    // would be registered (and unrolled) under `pathVar` instead of `guard`. We therefore bind it to
    // a fresh variable under `guard`. Where `guard` doesn't hold, the base check is false, so
    // the conjunction it is part of doesn't depend on the (unconstrained) variable.
    def guardedResult(pathVar: Variable, guard: Variable, res: Expr, name: String): Expr =
      if (guard == pathVar || res.isInstanceOf[BooleanLiteral]) res
      else {
        val newExpr: Variable = Variable.fresh(name, BooleanType(), true)
        storeExpr(newExpr)
        storeGuarded(guard, Equals(newExpr, res))
        newExpr
      }

    // A blocker under `pathVar` that the solver sets freely, under which a membership check
    // instantiates its counterexample (see the function case below).
    def membershipGuard(pathVar: Variable): Variable = {
      val choice = Variable.fresh("choice", BooleanType(), true)
      storeExpr(choice)
      val w = Variable.fresh("w", BooleanType(), true)
      storeCond(pathVar, w)
      iff(and(pathVar, choice), w)
      w
    }

    def rec(pathVar: Variable, tpe: Type, expr: Expr, state: RecursionState): Expr = tpe match {
      case tpe if !(generator `unroll` tpe) => BooleanLiteral(true) // nothing to do here!

      // A function `f` lies in `Pi(x: A). B` iff `A(x0) ==> B(f(x0))` holds for all `x0`. We check
      // this at fresh values `x0` that are assumed to lie in `A` whenever the guard `w` holds:
      // if `f` lies outside of the type, the solver can pick a counterexample for `x0` and set
      // `w`, and otherwise the result can only be false if `B(f(x0))` is false for some `x0` in
      // `A`, so the result is exact in models. The guard `w` is free so that types with an empty
      // domain don't make the path infeasible.
      //
      // The domains of quantifiers in positive polarity are checked the same way: there, the result
      // may only be false if the value lies outside of the type, as it disables the instantiation.
      case (_: FunctionType | _: PiType) if generator == MembershipGenerator || (inDomain && generator == ContractGenerator) =>
        val (params, to) = tpe match {
          case PiType(params, to) => (params, to)
          case FunctionType(from, to) => (from.map(tpe => ValDef.fresh("x", tpe, true)), to)
          case _ => throw new InternalSolverError(s"Unexpected function type: ${tpe.asString}")
        }

        val w = membershipGuard(pathVar)

        val (args, subst) = params.foldLeft((Seq.empty[Variable], Map.empty[ValDef, Expr])) {
          case ((args, subst), vd) =>
            val paramType = typeOps.replaceFromSymbols(subst, vd.tpe)
            val arg = Variable.fresh(vd.id.name, paramType.getType, true)
            storeExpr(arg)
            val (p, paramClauses) = mkTypeClauses(w, paramType, arg, localSubst)(using FreeGenerator)
            builder ++= paramClauses
            storeGuarded(w, p)
            (args :+ arg, subst + (vd -> arg))
        }

        val res = rec(w, typeOps.replaceFromSymbols(subst, to), Application(expr, args), state)
        implies(w, res)

      // Maps, sets and bags are checked the same way as functions: a map lies in `Map[A, B]` iff its
      // value at every key lies in `B`, and a set or bag lies in `Set[A]` or `Bag[A]` iff each of its
      // elements lies in `A`, so the result can only be false at a key or element that the solver
      // picks as a counterexample. Decomposing the value instead (see below) would let the solver
      // pick a decomposition whose parts lie outside of the type although the value doesn't, and
      // never completes for collections that may hold infinitely many elements. The keys of maps
      // must be unrefined, as the value of a map at a key outside of `A` must be its default.
      case MapType(from, to) if !(ContractUnrolling `unroll` from) &&
          (generator == MembershipGenerator || (inDomain && generator == ContractGenerator)) =>
        val w = membershipGuard(pathVar)
        val key = Variable.fresh("key", from, true)
        storeExpr(key)
        implies(w, rec(w, to, MapApply(expr, key), state))

      case SetType(base) if generator == MembershipGenerator || (inDomain && generator == ContractGenerator) =>
        val w = membershipGuard(pathVar)
        val elem = Variable.fresh("elem", base.getType, true)
        storeExpr(elem)
        storeGuarded(w, ElementOfSet(elem, expr))
        implies(w, rec(w, base, elem, state))

      case BagType(base) if generator == MembershipGenerator || (inDomain && generator == ContractGenerator) =>
        val w = membershipGuard(pathVar)
        val elem = Variable.fresh("elem", base.getType, true)
        storeExpr(elem)
        storeGuarded(w, GreaterThan(MultiplicityInBag(elem, expr), IntegerLiteral(0)))
        implies(w, rec(w, base, elem, state))

      case (_: FunctionType | _: PiType) => storeType(pathVar, tpe, expr, inDomain)

      case tp: TypeParameter if generator == FreeGenerator => typesManager.storeTypeParameter(tp)

      case RefinementType(vd, pred) =>
        val newExpr: Variable = Variable.fresh("lt", vd.getType, true)
        storeExpr(newExpr)

        storeGuarded(pathVar, Equals(newExpr, expr))

        val recBase = rec(pathVar, vd.tpe, expr, state)

        // The predicate may only be meaningful (e.g. it may contain assumptions) when `expr`
        // belongs to the base type, so its clauses are guarded by the base type check.
        // Otherwise, a predicate failing outside of the base type would falsify `pathVar`
        // instead of simply making the type check false.
        val predVar = guardedBy(pathVar, recBase, mayFalsifyPath(pred), "rp")

        val (p, predClauses) = mkExprClauses(predVar,
          exprOps.replaceFromSymbols(Map(vd -> newExpr), pred), localSubst)
        builder ++= predClauses

        and(recBase, guardedResult(pathVar, predVar, p, "rr"))

      case SigmaType(params, to) =>
        val (newExprs, recParams) = params.zipWithIndex.map { case (vd, i) =>
          val newExpr: Variable = Variable.fresh("lt", vd.getType, true)
          storeExpr(newExpr)

          storeGuarded(pathVar, Equals(newExpr, TupleSelect(expr, i + 1)))
          (newExpr, rec(pathVar, vd.tpe, newExpr, state))
        }.unzip

        // Similarly to refinements, the (dependent) last component is only checked
        // when the first components belong to their types.
        val toVar = guardedBy(pathVar, andJoin(recParams), mayFalsifyPath(to), "sp")

        val recTo = rec(toVar,
          typeOps.replaceFromSymbols((params zip newExprs).toMap, to),
          TupleSelect(expr, params.size + 1), state)

        andJoin(recParams :+ guardedResult(pathVar, toVar, recTo, "sr"))

      case adt: ADTType =>
        val sort = adt.getSort

        and(
          sort.invariant
            .filter(_ => generator == FreeGenerator)
            .map(_.applied(Seq(expr)))
            .getOrElse(BooleanLiteral(true)),
          if (sort.definition.isInductive && !state.recurseAdt) {
            storeType(pathVar, tpe, expr, inDomain)
          } else {
            val newExpr = Variable.fresh("e", BooleanType(), true)
            storeExpr(newExpr)

            val stored = for (tcons <- sort.constructors) yield {
              if (tcons.fields.exists(vd => generator `unroll` vd.tpe)) {
                val newBool: Variable = Variable.fresh("b", BooleanType(), true)
                storeCond(pathVar, newBool)

                // generate conditions for every ADT field to satisfy its type constraints,
                // but substitute field references as dependent on the current instance
                val fieldSubst = tcons.fields.map(vd => vd -> ADTSelector(expr, vd.id)).toMap
                val recProps = tcons.fields.map { vd =>
                  val fieldType = typeOps.replaceFromSymbols(fieldSubst, vd.tpe)
                  rec(newBool, fieldType, ADTSelector(expr, vd.id), state.copy(recurseAdt = false))
                }

                val recProp = andJoin(recProps)

                iff(and(pathVar, isCons(expr, tcons.id)), newBool)
                storeGuarded(newBool, Equals(newExpr, recProp))
                true
              } else {
                // Constructors without fields to check trivially satisfy the type. Otherwise `newExpr`
                // would be unconstrained for them, and the type check of a quantifier's domain could be
                // falsified to weaken the formula. The clause is only added for quantifier domains
                // (see `inDomain`), to keep the encoding unchanged elsewhere.
                if (inDomain) storeGuarded(pathVar, Implies(isCons(expr, tcons.id), newExpr))
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
          storeType(pathVar, tpe, expr, inDomain)
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
          decompositionKeys += keyExpr

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

          and(rec(pathVar, to, defaultExpr, state), newExpr, storeReads(pathVar, tpe, to, expr, inDomain))
        }

      case SetType(base) =>
        if (!state.recurseSet) {
          storeType(pathVar, tpe, expr, inDomain)
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
          decompositionKeys += elemExpr

          storeGuarded(pathVar, Equals(condVar, Equals(expr, FiniteSet(Seq(), base))))
          iff(and(pathVar, condVar), newBool1)
          iff(and(pathVar, not(condVar)), newBool2)

          storeGuarded(newBool1, newExpr)
          storeGuarded(newBool2, Equals(expr, SetUnion(FiniteSet(Seq(elemExpr), base), restExpr)))
          storeGuarded(newBool2, Equals(newExpr, and(
            rec(newBool2, tpe, restExpr, state.copy(recurseSet = false)),
            rec(newBool2, base, elemExpr, state)
          )))

          and(newExpr, storeReads(pathVar, tpe, base, expr, inDomain))
        }

      case BagType(base) =>
        if (!state.recurseBag) {
          storeType(pathVar, tpe, expr, inDomain)
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
          decompositionKeys += elemExpr

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

          and(newExpr, storeReads(pathVar, tpe, base, expr, inDomain))
        }

      case _ => throw new InternalSolverError(s"Unexpected unrollable: ${tpe.asString}")
    }

    val p = rec(pathVar, tpe, expr, RecursionState(true, true, true, true))
    (p, builder.result)
  }
}
