/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package evaluators

import org.scalatest.funsuite.AnyFunSuite

/** Evaluation of `forall`, `choose` and uninterpreted calls, which the evaluator hands to a solver. */
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

  test("a choice picks a value satisfying its predicate") {
    val res = "res" :: IntegerType()
    val pred = And(GreaterThan(res.toVariable, IntegerLiteral(5)), LessThan(res.toVariable, IntegerLiteral(7)))
    assert(value(exprOps.choose(res, pred)) == IntegerLiteral(6))
  }

  test("a choice without a solution is an error") {
    val res = "res" :: IntegerType()
    val pred = And(GreaterThan(res.toVariable, IntegerLiteral(5)), LessThan(res.toVariable, IntegerLiteral(6)))
    assert(!evaluate(exprOps.choose(res, pred)).isInstanceOf[EvaluationResults.Successful[?]])
  }

  test("an unconstrained choice picks its simplest value") {
    // The solver doesn't look for a value of the result's type, which may never end for an ADT
    // whose invariant only holds for infinite values (see Stainless's ForestNothing2).
    val res = "res" :: IntegerType()
    assert(value(exprOps.choose(res, BooleanLiteral(true))) == IntegerLiteral(0))
  }

  test("quantifiers are not evaluated when disabled") {
    val res = "res" :: IntegerType()
    val disabled = optEvalQuantifiers(false)
    assert(!evaluate(Forall(Seq(x), BooleanLiteral(true)), disabled).isInstanceOf[EvaluationResults.Successful[?]])
    assert(!evaluate(exprOps.choose(res, BooleanLiteral(true)), disabled).isInstanceOf[EvaluationResults.Successful[?]])
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
    val dependent = exprOps.choose(res, Equals(res.toVariable, exprOps.choose(inner, GreaterThan(inner.toVariable, IntegerLiteral(0)))))
    assert(!evaluate(dependent, solvers.optCheckModels(true)).isInstanceOf[EvaluationResults.Successful[?]])
    assert(value(dependent).isInstanceOf[IntegerLiteral])
  }

  test("a choice over a type parameter") {
    val tp = TypeParameter.fresh("T")
    val res = "res" :: tp
    assert(evaluate(exprOps.choose(res, BooleanLiteral(true))).isInstanceOf[EvaluationResults.Successful[?]])
  }

  val e = ValDef.fresh("e", IntegerType())
  val aboveFive = RefinementType(e, GreaterThan(e.toVariable, IntegerLiteral(5)))
  val noValues = RefinementType(e, BooleanLiteral(false))

  test("a choice respects the refinement of its result") {
    val res = "res" :: aboveFive
    value(exprOps.choose(res, BooleanLiteral(true))) match {
      case IntegerLiteral(n) => assert(n > 5)
      case v => fail(s"Expected an integer but got $v")
    }
    val empty = "empty" :: noValues
    assert(!evaluate(exprOps.choose(empty, BooleanLiteral(true))).isInstanceOf[EvaluationResults.Successful[?]])
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
      Forall(Seq(empty), BooleanLiteral(false)),
      exprOps.choose(x, GreaterThan(x.toVariable, IntegerLiteral(0)))
    )) assert(!evaluator.eval(expr, Model.empty(program)).isInstanceOf[EvaluationResults.Successful[?]], s"$expr should fail")
  }

  // f(n) ∈ { r | n < r && r < n + 2 }
  val n = "n" :: IntegerType()
  val r = "r" :: IntegerType()
  val f = FreshIdentifier("f")
  val successor = PiType(Seq(n), RefinementType(r,
    And(LessThan(n.toVariable, r.toVariable), LessThan(r.toVariable, Plus(n.toVariable, IntegerLiteral(2))))))
  def callF(arg: Expr) = UninterpretedCall(f, Seq(), Seq(arg), successor)

  test("uninterpreted calls outside the model satisfy the refinement of their result") {
    assert(value(callF(IntegerLiteral(5))) == IntegerLiteral(6))
    assert(value(Let(x, IntegerLiteral(2), callF(Plus(x.toVariable, IntegerLiteral(1))))) == IntegerLiteral(4))
  }

  test("uninterpreted calls outside the model are functions of their arguments") {
    val g = FreshIdentifier("g")
    val any = PiType(Seq(n), IntegerType())
    val evaluator = RecursiveEvaluator(program, TestContext.empty)
    def callG(arg: Expr) = UninterpretedCall(g, Seq(), Seq(arg), any)
    val expr = Equals(callG(IntegerLiteral(1)), callG(Minus(IntegerLiteral(2), IntegerLiteral(1))))
    assert(evaluator.eval(expr, Model.empty(program)) == EvaluationResults.Successful(BooleanLiteral(true)))
  }

  test("uninterpreted calls outside the model whose results have no value are errors") {
    val empty = PiType(Seq(n), RefinementType(r, LessThan(r.toVariable, r.toVariable)))
    assert(!evaluate(UninterpretedCall(f, Seq(), Seq(IntegerLiteral(0)), empty)).isInstanceOf[EvaluationResults.Successful[?]])
    assert(!evaluate(callF(IntegerLiteral(0)), optEvalQuantifiers(false)).isInstanceOf[EvaluationResults.Successful[?]])
  }

  test("uninterpreted calls that the model interprets aren't solved for") {
    val evaluator = RecursiveEvaluator(program, TestContext.empty)
    val m = "m" :: IntegerType()
    val model = Model(program)(Map.empty, Map((f, Seq.empty[Type]) -> Lambda(Seq(m), Plus(m.toVariable, IntegerLiteral(1)))))
    assert(evaluator.eval(callF(IntegerLiteral(5)), model) == EvaluationResults.Successful(IntegerLiteral(6)))
    val g = FreshIdentifier("g")
    val other = Model(program)(Map.empty, Map((g, Seq.empty[Type]) -> Lambda(Seq(m), m.toVariable)))
    assert(evaluator.eval(callF(IntegerLiteral(5)), other) == EvaluationResults.Successful(IntegerLiteral(6)))
  }
}
