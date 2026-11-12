/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package evaluators

import org.scalatest.funsuite.AnyFunSuite

/** Evaluation of `forall`, which the evaluator hands to a solver, and of uninterpreted calls, which
  * the model must interpret. */
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

  test("quantifiers are not evaluated when disabled") {
    val disabled = optEvalQuantifiers(false)
    assert(!evaluate(Forall(Seq(x), BooleanLiteral(true)), disabled).isInstanceOf[EvaluationResults.Successful[?]])
  }

  test("an evaluator reuses its forall results") {
    val evaluator = RecursiveEvaluator(program, TestContext.empty)
    val forall = Forall(Seq(x), GreaterThan(x.toVariable, IntegerLiteral(0)))
    val expr = And(Not(forall), Not(forall))
    assert(evaluator.eval(expr, Model.empty(program)) == EvaluationResults.Successful(BooleanLiteral(true)))
    assert(evaluator.eval(forall, Model.empty(program)) == EvaluationResults.Successful(BooleanLiteral(false)))
  }

  val e = ValDef.fresh("e", IntegerType())
  val aboveFive = RefinementType(e, GreaterThan(e.toVariable, IntegerLiteral(5)))
  val noValues = RefinementType(e, BooleanLiteral(false))

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
