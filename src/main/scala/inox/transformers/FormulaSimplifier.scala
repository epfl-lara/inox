/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

import evaluators.EvaluationResults._
import solvers.PurityOptions
import scala.util.chaining._

/** A simplifier of the formulas that the solvers are given: the simplification under path
  * conditions of [[SimplifierWithPC]], which here also does what helps the instantiation of
  * quantifiers and evaluates ground terms.
  *
  * In one traversal, the simplification applies the lambdas that the path binds, which inlines
  * those that are bound around quantifiers, simplifies the quantifiers, rewrites the sets, bags
  * and maps that quantifiers are instantiated on, inlines the functions that have quantifiers
  * (see [[inlines]]), lifts the assumptions of the subterms of an assumption and evaluates the
  * ground terms, whose values it then simplifies with: a conditional whose condition evaluates
  * is one of its branches.
  *
  * In the body of a lambda, a ground term is part of how the function is written, and functions
  * are compared as they are written: `x => x + 10 / 2` and `x => x + 5` are not the same
  * function. Such a term is only evaluated if each of its operations is pure whatever its
  * operands are, which a division is not, and neither is the call of a function whose recursion
  * is in the body of a lambda, like `zero = Lang(false, x => zero)`, whose value calls it again.
  *
  * All that is done to a formula is done by one simplifier, which records the steps of what it
  * does in the recorder that it is given with the formula (see
  * [[TransformationRecorder]]): the traversal has it in its path, and the simplifier itself
  * keeps nothing of a formula, so that one simplifier serves the simplifications that are
  * recorded and those that are not. */
trait FormulaSimplifier extends SimplifierWithPath { self =>

  import trees._
  import trees.exprOps._
  import symbols.{given, _}

  private given PurityOptions = opts

  /** The sets, bags and maps of several elements as updates of smaller ones, which the
    * instantiation of quantifiers matches on. */
  private def matcher(e: Expr): Option[Expr] = e match {
    case f @ FiniteSet(elems, base) if elems.nonEmpty =>
      Some(elems.foldLeft(FiniteSet(Seq.empty, base).copiedFrom(f): Expr)(SetAdd(_,_).copiedFrom(f)))
    case f @ FiniteBag(pairs :+ (pair @ (key, _)), base) if pairs.nonEmpty =>
      Some(pairs.foldRight((FiniteBag(Seq(pair), base).copiedFrom(f): Expr, Seq(key))) {
        case (pair @ (key, _), (bag, elems)) => (ifExpr(
          orJoin(elems.map(e => Equals(e, key).copiedFrom(f))).copiedFrom(f),
          bag,
          BagUnion(bag, FiniteBag(Seq(pair), base).copiedFrom(f)).copiedFrom(f)
        ).copiedFrom(f), key +: elems)
      }._1)
    case f @ FiniteMap(pairs, dflt, from, to) if pairs.nonEmpty =>
      Some(pairs.foldLeft(FiniteMap(Seq.empty, dflt, from, to).copiedFrom(f): Expr) {
        (map, pair) => MapUpdated(map, pair._1, pair._2).copiedFrom(f)
      })
    case _ => None
  }

  // The call edges of the functions and which of them are inlined (see [[inlines]]), which only
  // depend on the symbols
  private val callees = new java.util.concurrent.ConcurrentHashMap[Identifier, Set[Identifier]]
  private val inlined = new java.util.concurrent.ConcurrentHashMap[Identifier, java.lang.Boolean]
  private val recursions = new java.util.concurrent.ConcurrentHashMap[Identifier, java.lang.Boolean]
  private val suspendedCallees = new java.util.concurrent.ConcurrentHashMap[Identifier, Set[Identifier]]
  private val suspendedRecursions = new java.util.concurrent.ConcurrentHashMap[Identifier, java.lang.Boolean]

  private def calleesOf(id: Identifier): Set[Identifier] =
    callees.computeIfAbsent(id, id => collect[Identifier] {
      case fi: FunctionInvocation => Set(fi.id)
      case Equals(IsTyped(_, adt: ADTType), _) if adt.getSort.hasEquality => Set(adt.getSort.equality.get.id)
      case _ => Set.empty
    } (getFunction(id).fullBody))

  /** Whether the function `id` is called from its own body, directly or not. */
  private def recursive(id: Identifier): Boolean =
    recursions.computeIfAbsent(id, id => java.lang.Boolean.valueOf {
      val seen = scala.collection.mutable.Set.empty[Identifier]
      var todo = calleesOf(id).toList
      while (todo.nonEmpty) {
        val callee = todo.head
        todo = todo.tail
        if (seen.add(callee)) todo = calleesOf(callee).toList ++ todo
      }
      seen(id)
    }).booleanValue

  // the functions that each function calls in the bodies of its lambdas
  private def suspendedCalleesOf(id: Identifier): Set[Identifier] =
    suspendedCallees.computeIfAbsent(id, id => collect[Identifier] {
      case Lambda(_, body) => collect[Identifier] { case fi: FunctionInvocation => Set(fi.id) case _ => Set.empty } (body)
      case _ => Set.empty
    } (getFunction(id).fullBody))

  /** Whether the function `id` is called from its own body, directly or not, through a call in
    * the body of a lambda: its value is then a function that calls it again, like that of
    * `zero = Lang(false, x => zero)`. */
  private def suspendedRecursive(id: Identifier): Boolean =
    suspendedRecursions.computeIfAbsent(id, id => java.lang.Boolean.valueOf {
      // the functions that are reached, and whether through a call in a lambda
      val seen = scala.collection.mutable.Set.empty[(Identifier, Boolean)]
      var todo: List[(Identifier, Boolean)] = List(id -> false)
      var found = false
      while (todo.nonEmpty && !found) {
        val (caller, suspended) = todo.head
        todo = todo.tail
        val inLambdas = suspendedCalleesOf(caller)
        for (callee <- calleesOf(caller); next = callee -> (suspended || inLambdas(callee))) {
          if (next == (id -> true)) found = true
          else if (seen.add(next)) todo ::= next
        }
      }
      found
    }).booleanValue

  /** Whether the calls of the function `id` are inlined: it has a quantifier outside of
    * assumptions, which then has the polarity of the call, and is not (mutually) recursive. Calls
    * are followed through the equalities of sorts, which count as calls of the equality function
    * of the sort.
    *
    * The equalities of a sort whose equality function is inlined are not inlined themselves:
    * they are kept as equalities, of which the solvers know more than the function says (see
    * `EqualityTemplates`). The quantifiers of the function are encoded at the polarity of the
    * equality where its template is generated (see `TemplateGenerator`). */
  def inlines(id: Identifier): Boolean = {
    def hasForall(e: Expr): Boolean = e match {
      case _: Forall => true
      case Assume(_, body) => hasForall(body)
      case Operator(es, _) => es.exists(hasForall)
    }


    inlined.computeIfAbsent(id, id => java.lang.Boolean.valueOf(
      hasForall(getFunction(id).fullBody) && !recursive(id)
    )).booleanValue
  }

  /** Whether each operation of `e` is pure whatever its operands are: with variables for its
    * operands, it is pure without assuming that it is checked. The purity of a function doesn't
    * look at the bodies of its lambdas: a function whose recursion is in one is pure, and its
    * value calls it again, so its call is not such an operation. The bodies of the lambdas of
    * `e`, which the term doesn't evaluate, are not looked at. */
  private def total(e: Expr): Boolean = e match {
    case _: Lambda => true
    case fi: FunctionInvocation if suspendedRecursive(fi.id) => false
    case Operator(es, recons) =>
      es.forall(total) && isAlwaysPure(recons(es.map(e => Variable.fresh("x", e.getType))))
  }

  /** The value of the ground term `e`, if `evaluator` evaluates it and it is pure. In the body
    * of a lambda, where the term is part of how the function is written and functions are
    * compared as they are written, it is only evaluated if it is [[total]]: `10 / 2` stays in
    * `x => x + 10 / 2`. */
  private def evaluated(e: Expr, path: Env, evaluator: Expr => Option[Expr]): Option[Expr] =
    if (!(if (path.underLambda) total(e) else symbols.isPure(e))) None
    else evaluator(e).map { v =>
      val value = freshenLocals(v)
      val r = path.recorder
      if (r.active) r.at(e)(value.tap(recordEvaluation(r, e, _)))
      value
    }

  /** Evaluates the ground terms of `e`, from the largest ones, with `evaluator`. */
  private def evaluatedIn(e: Expr, path: Env, evaluator: Expr => Option[Expr]): Expr = {
    val r = path.recorder
    def rec(e: Expr, path: Env): Expr = {
      def children: Expr = {
        val Operator(es, recons) = e: @unchecked
        val inner = e match { case _: Lambda => path.inLambda case _ => path }
        val res = es.map(rec(_, inner))
        if ((res zip es).forall(p => p._1 eq p._2)) e else recons(res).copiedFrom(e)
      }
      def here: Expr =
        if (isGround(e) && !isValue(e)) evaluated(e, path, evaluator).getOrElse(children)
        else children
      if (!r.active) here else r.at(e)(here)
    }
    rec(e, path)
  }

  /** Simplifies `e` under `path`, and evaluates what it becomes when that is ground and the path
    * has an evaluator. The term is simplified first, so that what the simplification does of a
    * ground term is done by its rules, and recorded as their steps. */
  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = {
    val res = super.simplify(e, path)
    val evaluator = path.evaluator
    if ((evaluator eq null) || !isGround(res._1) || isValue(res._1)) res
    else evaluated(res._1, path, evaluator).fold(res)(value => (value, true))
  }

  /** Evaluates the ground terms of `e`, where a binding to a ground term was inlined: these are
    * not simplified again. */
  override protected def substituted(e: Expr, path: Env): Expr = {
    val evaluator = path.evaluator
    if (evaluator eq null) e else evaluatedIn(e, path, evaluator)
  }

  /** The simplification under path conditions, which also
    * - rewrites the terms that [[matcher]] does, for the instantiation of quantifiers;
    * - inlines the calls of the functions that have quantifiers (see [[inlines]]), which gives
    *   the quantifiers the polarity of the call;
    * - lifts the assumptions of the subterms of an assumption into it. */
  override protected def simplifyCore(e: Expr, path: Env): (Expr, Boolean) = matcher(e) match {
    case Some(m) =>
      recorded("matchers", m, path)
      simplify(m, path)

    case None => e match {
      case l: Lambda => super.simplifyCore(l, path.inLambda)

      // the call unfolds into the body under the bindings of its parameters, which `inlined`
      // then drops where they are not used
      case fi: FunctionInvocation if inlines(fi.id) =>
        val inlined = fi.inlined
        recorded("unfold", unfolded(fi), path)
        recorded("logic", inlined, path)
        simplify(inlined, path)

      case _: Assume => super.simplifyCore(e, path) match {
        case (assumption: Assume, pure) => (liftedAssumptions(assumption, path), pure)
        case res => res
      }

      case _ => super.simplifyCore(e, path)
    }
  }

  /** The simplified assumption `assumption` with the assumptions of its subterms lifted into
    * its predicate, which is then simplified again. */
  private def liftedAssumptions(assumption: Assume, path: Env): Expr = {
    val Assume(pred, body) = assumption
    val (predAssumptions, newPred) = liftAssumptions(pred)
    val (bodyAssumptions, newBody) = liftAssumptions(body)
    if (predAssumptions.isEmpty && bodyAssumptions.isEmpty) assumption else {
      val lifted = andJoin(predAssumptions ++ (newPred +: bodyAssumptions))
      // The `logic` rule of certificates doesn't look into lambdas and quantifiers: an
      // assumption that is lifted out of one is not a step of that rule.
      def underBinders(e: Expr): Int = count {
        case Lambda(_, body) => count { case _: Assume => 1; case _ => 0 } (body)
        case Forall(_, body) => count { case _: Assume => 1; case _ => 0 } (body)
        case _ => 0
      } (e)
      val to = Assume(lifted, newBody).copiedFrom(assumption)
      recorded(if (underBinders(assumption) == underBinders(to)) "logic" else "lift-assumptions", to, path)
      val (rp, _) = simplify(lifted, path)
      step("logic", assume(rp, newBody).copiedFrom(assumption), path)
    }
  }

  /** The steps of the evaluation of `e` to `value`, when the simplification is recorded. The
    * evaluator doesn't tell its steps: they are recorded for the evaluations that unfold
    * constants of the program, select fields of their values and test their constructors,
    * and the others are one step, of the rule `evaluate`. */
  private def recordEvaluation(r: Recorder, e: Expr, value: Expr): Unit = {
    if (r.active && e != value) {
      def steps(e: Expr): Expr = e match {
        case fi @ FunctionInvocation(_, _, Seq()) if !isValue(e) =>
          val body = unfolded(fi)
          r.rewrite("unfold", body)
          if (isValue(body)) body else steps(body)
        case ADTSelector(adt, selector) =>
          r.at(adt)(steps(adt)) match {
            case v @ ADT(id, tps, args) =>
              val field = args(v.getConstructor.definition.selectorID2Index(selector))
              r.rewrite("select", field)
              field
            case _ => r.node
          }
        case IsConstructor(adt, id) =>
          r.at(adt)(steps(adt)) match {
            case ADT(cons, _, _) =>
              val res = BooleanLiteral(cons == id)
              r.rewrite("logic", res)
              res
            case _ => r.node
          }
        case _ => e
      }
      val res = steps(e)
      r.rewrite(if (sameUpToLocals(res, value)) "rename" else "evaluate", value)
    }
  }

  /** Simplify all the pure and ground sub-expressions of the given expression,
    * by evaluating them using [[inox.evaluators.Evaluator]].
    * If `force` is omitted, the given expression will only be evaluated if it is
    * ground, pure, and does not contain uninterpreted calls or quantifiers.
    */
  def simplifyGround(expr: Expr, reportErrors: Boolean = false)(using sem: symbols.Semantics, ctx: Context): Expr = {
    val evalCtx = ctx.withOpts(evaluators.optEvalQuantifiers(false))
    val evaluator = sem.getEvaluator(using evalCtx)

    case class SimplifyGroundError(expr: Expr, result: Result[Expr]) {
      def errMsg: String = result match {
        case RuntimeError(msg) =>
          s"runtime error: $msg"
        case EvaluatorError(msg) =>
          s"evaluator error: $msg"
        case _ => ""
      }
      override def toString: String = {
        s"Forced evaluation of expression @ ${expr.getPos} failed because of a $errMsg"
      }
    }

    def evalChildren(e: Expr)(using PurityOptions): Expr = e match {
      case Operator(es, recons) => recons(es.map(rec))
    }

    // TODO: Should we run this within a fixpoint with simplifyByConstructor?
    def rec(e: Expr)(using PurityOptions): Expr = e match {
      case e if isValue(e) =>
        e
      case e if isGround(e) && symbols.isPure(e) =>
        val evaluated = evaluator.eval(e)
        evaluated.result.map { v =>
          val value = freshenLocals(v)
          value
        }.getOrElse {
          if (reportErrors) ctx.reporter.error(SimplifyGroundError(e, evaluated))
          evalChildren(e)
        }
      case l: Lambda =>
        evalChildren(l)(using PurityOptions.unchecked)
      case e =>
        evalChildren(e)
    }

    rec(expr)(using opts)
  }

  /** Simplifies the formula `e`, for the solvers: simplifies it under its path conditions,
    * and evaluates its ground subterms as it does. */
  def simplifyFormula(e: Expr, r: Recorder = noRecorder)(using ctx: Context, sem: symbols.Semantics): Expr = {
    val evaluator = sem.getEvaluator(using ctx.withOpts(evaluators.optEvalQuantifiers(false)))
    val path = Env.of(r, (e: Expr) => evaluator.eval(e).result)
    if (!r.active) transform(e, path) else r.at(e, "simplify")(transform(e, path))
  }
}
