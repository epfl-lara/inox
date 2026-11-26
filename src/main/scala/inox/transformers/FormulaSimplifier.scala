/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

import evaluators.EvaluationResults._
import solvers.PurityOptions
import utils.fixpoint

/** A simplifier of the formulas that the solvers are given: the simplification under path
  * conditions of [[SimplifierWithPC]], which here also rewrites the sets, bags and maps that
  * quantifiers are instantiated on, with the passes that go before and after it for formulas
  * (the lifting of assumptions, the inlining that helps the instantiation of quantifiers, and
  * the evaluation of ground terms).
  *
  * The lambdas that are bound around quantifiers are inlined by the simplification under path
  * conditions itself, as it applies the lambdas that the path binds, and so are the quantifiers
  * simplified.
  *
  * All that is done to a formula is done by one simplifier, which records the steps of what it
  * does in its `recorder`, when it has one (see [[TransformationRecorder]]). */
trait FormulaSimplifier extends SimplifierWithPC { self =>
  import trees._
  import trees.exprOps._
  import symbols.{given, _}

  private given PurityOptions = opts

  /** `postMap`, which records the rewrites when the simplification is recorded (see
    * `TransformationRecorder.postMap`). */
  private def recordedPostMap(rule: String)(f: Expr => Option[Expr])(record: (Expr, Expr) => Unit = (_, _) => ())(e: Expr): Expr = {
    val r = recorder
    if (r eq null) postMap(f)(e) else r.postMap(rule)(f)(record)(e)
  }

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

  /** The simplification under path conditions, which also rewrites the terms that [[matcher]]
    * does, for the instantiation of quantifiers. */
  override protected def simplifyCore(e: Expr, path: Env): (Expr, Boolean) =
    matcher(e) match {
      case Some(m) =>
        recorded("matchers", m)
        simplify(m, path)
      case None => super.simplifyCore(e, path)
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

  /** Pre-processing for solvers that handle universal quantification
    * in order to increase the precision of polarity analysis for
    * quantification instantiations.
    *
    * These are the passes that go before the simplification under path conditions, which does
    * the rest (see [[simplifyFormula]]).
    */
  def simplifyForalls(e: Expr): Expr = {

    def inlineFunctions(e: Expr): Expr = {
      val toInline = forallInlining.toInline(e)

      def inlineExpr(e: Expr): Expr = recordedPostMap("inline-equality") {
        case fi: FunctionInvocation if toInline(fi.id) =>
          Some(fi.inlined)
        case Equals(IsTyped(e1, adt: ADTType), e2)
        if adt.getSort.hasEquality && toInline(adt.getSort.equality.get.id) =>
          Some(adt.getSort.equality.get.applied(Seq(e1, e2)).inlined)
        case _ => None
      } {
        // the call unfolds into the body under the bindings of its parameters, which `inlined`
        // then drops where they are not used
        case (fi: FunctionInvocation, inlined) =>
          recorded("unfold", unfolded(fi))
          recorded("logic", inlined)
        // the call of the equality function of a sort is not unfolded in steps
        case _ =>
      } (e)

      fixpoint(inlineExpr)(e)
    }

    /* Weaker variant of conjunctive normal form */
    def normalizeClauses(e: Expr): Expr = e match {
      case Not(Not(e)) => normalizeClauses(e)
      case Not(Or(es)) => andJoin(es.map(e => normalizeClauses(Not(e))))
      case Not(Implies(e1, e2)) => and(normalizeClauses(e1), normalizeClauses(Not(e2)))
      case And(es) => andJoin(es map normalizeClauses)
      case _ => e
    }

    val simp: Expr => Expr =
      recordedPass("normalize", (e: Expr) => { val n = normalizeClauses(e); recorded("logic", n); n }) compose
      recordedPass("lift-assumptions", (e: Expr) => simplifyAssumptions(e))  compose
      recordedPass("inline-functions", (e: Expr) => inlineFunctions(e))
    simp(e)
  }

  /** Lifts the assumptions of the subterms of `expr` to the assumptions that they are under. */
  def simplifyAssumptions(expr: Expr): Expr = recordedPostMap("lift-assumptions") {
    case Assume(pred, body) =>
      val (predAssumptions, newPred) = liftAssumptions(pred)
      val (bodyAssumptions, newBody) = liftAssumptions(body)
      Some(assume(andJoin(predAssumptions ++ (newPred +: bodyAssumptions)), newBody))
    case _ => None
  } { (from, to) =>
    // The `logic` rule of certificates doesn't look into lambdas and quantifiers: an assumption
    // that is lifted out of one is not a step of that rule.
    def underBinders(e: Expr): Int = count {
      case Lambda(_, body) => count { case _: Assume => 1; case _ => 0 } (body)
      case Forall(_, body) => count { case _: Assume => 1; case _ => 0 } (body)
      case _ => 0
    } (e)
    if (underBinders(from) == underBinders(to)) recorded("logic", to)
  } (expr)

  /** Simplifies the formula `e`, for the solvers: lifts its assumptions, simplifies it for
    * the instantiation of its quantifiers, simplifies it under its path conditions, and
    * evaluates its ground subterms. */
  def simplifyFormula(e: Expr)(using ctx: Context, sem: symbols.Semantics): Expr = {
    val simp: Expr => Expr =
      recordedPass("evaluate", (e: Expr) => simplifyGround(e))               compose
      recordedPass("simplify", (e: Expr) => transform(e, initEnv))           compose
      ((e: Expr) => simplifyForalls(e))                                      compose
      recordedPass("lift-assumptions", (e: Expr) => simplifyAssumptions(e))
    simp(e)
  }

  /** A pass of a simplification: when it is recorded, what the pass makes of the term without
    * recording how is a step of the rule `rule`. */
  private def recordedPass(rule: String, pass: Expr => Expr): Expr => Expr = (e: Expr) => {
    val r = recorder
    if (r eq null) pass(e) else r.at(e, rule)(pass(e))
  }
}
