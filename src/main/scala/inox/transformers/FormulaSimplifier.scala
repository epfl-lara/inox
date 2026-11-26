/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

import evaluators.EvaluationResults._
import solvers.PurityOptions

/** A simplifier of the formulas that the solvers are given: the simplification under path
  * conditions of [[SimplifierWithPC]], which here also does what helps the instantiation of
  * quantifiers, followed by the evaluation of ground terms.
  *
  * In one traversal, the simplification applies the lambdas that the path binds, which inlines
  * those that are bound around quantifiers, simplifies the quantifiers, rewrites the sets, bags
  * and maps that quantifiers are instantiated on, inlines the functions that have quantifiers
  * (see `forallInlining`) and lifts the assumptions of the subterms of an assumption.
  *
  * The ground terms are evaluated by a pass of its own, after the traversal: the traversal
  * compares terms that an evaluation would make the same, like the lambdas `x => x + 10 / 2`
  * and `x => x + 5`, which are not the same function when functions are compared as they are
  * written.
  *
  * All that is done to a formula is done by one simplifier, which records the steps of what it
  * does in its `recorder`, when it has one (see [[TransformationRecorder]]). */
trait FormulaSimplifier extends SimplifierWithPC { self =>
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

  // The functions that the simplification of a formula inlines (see [[simplifyFormula]]). The
  // simplifier of a program is shared by the threads that simplify its formulas.
  private val inlining = new ThreadLocal[Set[Identifier]] { override def initialValue: Set[Identifier] = Set.empty }

  /** The simplification under path conditions, which also
    * - rewrites the terms that [[matcher]] does, for the instantiation of quantifiers;
    * - inlines the calls of the functions that have quantifiers, and the equalities of the sorts
    *   whose equality function is one of them, which increases the precision of the polarity
    *   analysis of the instantiation of quantifiers;
    * - lifts the assumptions of the subterms of an assumption into it. */
  override protected def simplifyCore(e: Expr, path: Env): (Expr, Boolean) = matcher(e) match {
    case Some(m) =>
      recorded("matchers", m)
      simplify(m, path)

    case None => e match {
      // the call unfolds into the body under the bindings of its parameters, which `inlined`
      // then drops where they are not used
      case fi: FunctionInvocation if inlining.get.contains(fi.id) =>
        val inlined = fi.inlined
        recorded("unfold", unfolded(fi))
        recorded("logic", inlined)
        simplify(inlined, path)

      // the call of the equality function of a sort is not unfolded in steps
      case Equals(IsTyped(e1, adt: ADTType), e2)
      if adt.getSort.hasEquality && inlining.get.contains(adt.getSort.equality.get.id) =>
        val inlined = adt.getSort.equality.get.applied(Seq(e1, e2)).inlined
        recorded("inline-equality", inlined)
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
      recorded(if (underBinders(assumption) == underBinders(to)) "logic" else "lift-assumptions", to)
      val (rp, _) = simplify(lifted, path)
      step("logic", assume(rp, newBody).copiedFrom(assumption))
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

    // The steps of the evaluation of `e` to `value`, when the simplification is recorded. The
    // evaluator doesn't tell its steps: they are recorded for the evaluations that unfold
    // constants of the program, select fields of their values and test their constructors,
    // and the others are one step, of the rule `evaluate`.
    def record(e: Expr, value: Expr): Unit = {
      val r = recorder
      if ((r ne null) && r.active && e != value) {
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

    // TODO: Should we run this within a fixpoint with simplifyByConstructor?
    def rec(e: Expr)(using PurityOptions): Expr = recordedAt(e)(e match {
      case e if isValue(e) =>
        e
      case e if isGround(e) && symbols.isPure(e) =>
        val evaluated = evaluator.eval(e)
        evaluated.result.map { v =>
          val value = freshenLocals(v)
          record(e, value)
          value
        }.getOrElse {
          if (reportErrors) ctx.reporter.error(SimplifyGroundError(e, evaluated))
          evalChildren(e)
        }
      case l: Lambda =>
        evalChildren(l)(using PurityOptions.unchecked)
      case e =>
        evalChildren(e)
    })

    rec(expr)(using opts)
  }

  /** Simplifies the formula `e`, for the solvers: simplifies it under its path conditions,
    * which inlines the functions that `forallInlining` says to, and evaluates its ground
    * subterms. */
  def simplifyFormula(e: Expr)(using ctx: Context, sem: symbols.Semantics): Expr = {
    val simp: Expr => Expr =
      recordedPass("evaluate", (e: Expr) => simplifyGround(e))               compose
      recordedPass("simplify", (e: Expr) => {
        val outer = inlining.get
        inlining.set(forallInlining.toInline(e))
        try transform(e, initEnv) finally inlining.set(outer)
      })
    simp(e)
  }

  /** A pass of a simplification: when it is recorded, what the pass makes of the term without
    * recording how is a step of the rule `rule`. */
  private def recordedPass(rule: String, pass: Expr => Expr): Expr => Expr = (e: Expr) => {
    val r = recorder
    if (r eq null) pass(e) else r.at(e, rule)(pass(e))
  }
}
