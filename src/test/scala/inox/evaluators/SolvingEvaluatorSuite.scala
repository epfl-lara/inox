/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package evaluators

import org.scalatest.funsuite.AnyFunSuite

/** Evaluation of `forall`, which the evaluator hands to a solver, of choices, which it solves for
  * on demand (see [[SolvingEvaluator.solveFor]]), and of uninterpreted calls, which the model must
  * interpret. */
class SolvingEvaluatorSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl._

  val program = InoxProgram(NoSymbols)

  def evaluate(expr: Expr, opts: OptionValue[?]*): EvaluationResults.Result[Expr] = {
    val evaluator = RecursiveEvaluator(program, TestContext(Options(opts)))
    evaluator.eval(expr, Model.empty(program))
  }

  def value(expr: Expr): Expr = evaluate(expr) match {
    case EvaluationResults.Successful(res) => res
    case res => fail(s"Expected a value but got $res")
  }

  def solve(res: ValDef, pred: Expr, opts: OptionValue[?]*): Option[Expr] =
    scala.util.Try(RecursiveEvaluator(program, TestContext(Options(opts))).solveFor(res, pred)).toOption

  def choice(res: ValDef, pred: Expr): Expr = solve(res, pred).getOrElse(fail(s"Expected a value for $res"))

  val x = "x" :: IntegerType()

  test("forall that holds") {
    assert(value(Forall(Seq(x), GreaterThan(Plus(x.toVariable, IntegerLiteral(1)), x.toVariable))) == BooleanLiteral(true))
  }

  test("forall with a counterexample") {
    assert(value(Forall(Seq(x), GreaterThan(x.toVariable, IntegerLiteral(0)))) == BooleanLiteral(false))
  }

  test("forall under a binding") {
    val y = "y" :: IntegerType()
    val expr = Let(y, IntegerLiteral(3), Forall(Seq(x), Implies(GreaterThan(x.toVariable, y.toVariable), GreaterThan(x.toVariable, IntegerLiteral(2)))))
    assert(value(expr) == BooleanLiteral(true))
  }

  test("forall over an unused type parameter") {
    val tp = TypeParameter.fresh("T")
    val t = "t" :: tp
    assert(value(Forall(Seq(t), BooleanLiteral(false))) == BooleanLiteral(false))
    assert(value(Forall(Seq(t, x), GreaterThan(Plus(x.toVariable, IntegerLiteral(1)), x.toVariable))) == BooleanLiteral(true))
  }

  test("a choice picks a value satisfying its predicate") {
    val res = "res" :: IntegerType()
    val pred = And(GreaterThan(res.toVariable, IntegerLiteral(5)), LessThan(res.toVariable, IntegerLiteral(7)))
    assert(choice(res, pred) == IntegerLiteral(6))
  }

  test("a choice without a solution is an error") {
    val res = "res" :: IntegerType()
    val pred = And(GreaterThan(res.toVariable, IntegerLiteral(5)), LessThan(res.toVariable, IntegerLiteral(6)))
    assert(solve(res, pred).isEmpty)
  }

  test("an unconstrained choice picks its simplest value") {
    // The solver doesn't look for a value of the result's type, which may never end for an ADT
    // whose invariant only holds for infinite values (see Stainless's ForestNothing2).
    val res = "res" :: IntegerType()
    assert(choice(res, BooleanLiteral(true)) == IntegerLiteral(0))
  }

  test("quantifiers are not evaluated when disabled") {
    val res = "res" :: IntegerType()
    val disabled = optEvalQuantifiers(false)
    assert(!evaluate(Forall(Seq(x), BooleanLiteral(true)), disabled).isInstanceOf[EvaluationResults.Successful[?]])
    assert(solve(res, BooleanLiteral(true), disabled).isEmpty)
  }

  test("an evaluator reuses its forall results") {
    val evaluator = RecursiveEvaluator(program, TestContext.empty)
    val forall = Forall(Seq(x), GreaterThan(x.toVariable, IntegerLiteral(0)))
    val expr = And(Not(forall), Not(forall))
    assert(evaluator.eval(expr, Model.empty(program)) == EvaluationResults.Successful(BooleanLiteral(true)))
    assert(evaluator.eval(forall, Model.empty(program)) == EvaluationResults.Successful(BooleanLiteral(false)))
  }

  test("a choice depending on another choice is an error when checking models") {
    val res = "res" :: IntegerType()
    val inner = "inner" :: IntegerType()
    val dependent = Equals(res.toVariable, exprOps.choose(inner, GreaterThan(inner.toVariable, IntegerLiteral(0))))
    assert(solve(res, dependent, solvers.optCheckModels(true)).isEmpty)
    assert(choice(res, dependent).isInstanceOf[IntegerLiteral])
  }

  test("a choice over a type parameter") {
    val tp = TypeParameter.fresh("T")
    val res = "res" :: tp
    assert(solve(res, BooleanLiteral(true)).isDefined)
  }

  val e = ValDef.fresh("e", IntegerType())
  val aboveFive = RefinementType(e, GreaterThan(e.toVariable, IntegerLiteral(5)))
  val noValues = RefinementType(e, BooleanLiteral(false))

  test("a choice respects the refinement of its result") {
    val res = "res" :: aboveFive
    choice(res, BooleanLiteral(true)) match {
      case IntegerLiteral(n) => assert(n > 5)
      case v => fail(s"Expected an integer but got $v")
    }
    val empty = "empty" :: noValues
    assert(solve(empty, BooleanLiteral(true)).isEmpty)
  }

  test("forall over refined types") {
    val b = "b" :: aboveFive
    assert(value(Forall(Seq(b), GreaterThan(b.toVariable, IntegerLiteral(3)))) == BooleanLiteral(true))
    assert(value(Forall(Seq(b), GreaterThan(b.toVariable, IntegerLiteral(6)))) == BooleanLiteral(false))
    // A forall over a type without values holds, even when its body doesn't.
    val empty = "empty" :: noValues
    assert(value(Forall(Seq(empty), BooleanLiteral(false))) == BooleanLiteral(true))
    assert(value(Forall(Seq(empty, x), GreaterThan(x.toVariable, IntegerLiteral(0)))) == BooleanLiteral(true))
  }

  test("interrupted quantifiers are errors") {
    val ctx = TestContext.empty
    val evaluator = RecursiveEvaluator(program, ctx)
    ctx.interruptManager.interrupt()
    val empty = "empty" :: noValues
    for (expr <- Seq(
      Forall(Seq(x), GreaterThan(x.toVariable, IntegerLiteral(0))),
      Forall(Seq(empty), BooleanLiteral(false))
    )) assert(!evaluator.eval(expr, Model.empty(program)).isInstanceOf[EvaluationResults.Successful[?]], s"$expr should fail")
    assert(scala.util.Try(evaluator.solveFor(x, GreaterThan(x.toVariable, IntegerLiteral(0)))).isFailure)
  }

  // f(n) ∈ { r | n < r && r < n + 2 }
  val n = "n" :: IntegerType()
  val r = "r" :: IntegerType()
  val f = FreshIdentifier("f")
  val successor = PiType(Seq(n), RefinementType(r,
    And(LessThan(n.toVariable, r.toVariable), LessThan(r.toVariable, Plus(n.toVariable, IntegerLiteral(2))))))
  def callF(arg: Expr) = UninterpretedCall(f, Seq(), Seq(arg), successor)

  test("uninterpreted calls outside the model are errors") {
    assert(!evaluate(callF(IntegerLiteral(5))).isInstanceOf[EvaluationResults.Successful[?]])
    val m = "m" :: IntegerType()
    val g = FreshIdentifier("g")
    val other = Model(program)(Map.empty, Map((g, Seq.empty[Type]) -> Lambda(Seq(m), m.toVariable)))
    val evaluator = RecursiveEvaluator(program, TestContext.empty)
    assert(!evaluator.eval(callF(IntegerLiteral(5)), other).isInstanceOf[EvaluationResults.Successful[?]])
  }

  test("uninterpreted calls that the model interprets") {
    val evaluator = RecursiveEvaluator(program, TestContext.empty)
    val m = "m" :: IntegerType()
    val model = Model(program)(Map.empty, Map((f, Seq.empty[Type]) -> Lambda(Seq(m), Plus(m.toVariable, IntegerLiteral(1)))))
    assert(evaluator.eval(callF(IntegerLiteral(5)), model) == EvaluationResults.Successful(IntegerLiteral(6)))
  }
}
