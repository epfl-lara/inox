/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package evaluators

import org.scalatest._

class EvaluatorSuite extends FunSuite {
  import inox.trees._

  val ctx = TestContext.empty

  val symbols = new Symbols(Map.empty, Map.empty)
  def evaluator(ctx: Context): DeterministicEvaluator { val program: InoxProgram } = {
    val program = InoxProgram(ctx, symbols)
    RecursiveEvaluator.default(program)
  }

  test("Literals") {
    val e = evaluator(ctx)

    eval(e, BooleanLiteral(true))   === BooleanLiteral(true)
    eval(e, BooleanLiteral(false))  === BooleanLiteral(false)
    eval(e, IntLiteral(0))          === IntLiteral(0)
    eval(e, IntLiteral(42))         === IntLiteral(42)
    eval(e, UnitLiteral())          === UnitLiteral()
    eval(e, IntegerLiteral(0))      === IntegerLiteral(0)
    eval(e, IntegerLiteral(42))     === IntegerLiteral(42)
    eval(e, FractionLiteral(0 ,1))  === FractionLiteral(0 ,1)
    eval(e, FractionLiteral(42 ,1)) === FractionLiteral(42, 1)
    eval(e, FractionLiteral(26, 3)) === FractionLiteral(26, 3)
  }

  test("BitVector Arithmetic") {
    val e = evaluator(ctx)

    eval(e, Plus(IntLiteral(3), IntLiteral(5)))  === IntLiteral(8)
    eval(e, Plus(IntLiteral(0), IntLiteral(5)))  === IntLiteral(5)
    eval(e, Plus(IntLiteral(1), IntLiteral(-2)))  === IntLiteral(-1)
    eval(e, Plus(IntLiteral(Int.MaxValue), IntLiteral(1))) === IntLiteral(Int.MinValue)
    eval(e, Times(IntLiteral(3), IntLiteral(3))) === IntLiteral(9)
  }

  test("eval bitwise operations") {
    val e = evaluator(ctx)

    eval(e, BVAnd(IntLiteral(3), IntLiteral(1))) === IntLiteral(1)
    eval(e, BVAnd(IntLiteral(3), IntLiteral(3))) === IntLiteral(3)
    eval(e, BVAnd(IntLiteral(5), IntLiteral(3))) === IntLiteral(1)
    eval(e, BVAnd(IntLiteral(5), IntLiteral(4))) === IntLiteral(4)
    eval(e, BVAnd(IntLiteral(5), IntLiteral(2))) === IntLiteral(0)

    eval(e, BVOr(IntLiteral(3), IntLiteral(1))) === IntLiteral(3)
    eval(e, BVOr(IntLiteral(3), IntLiteral(3))) === IntLiteral(3)
    eval(e, BVOr(IntLiteral(5), IntLiteral(3))) === IntLiteral(7)
    eval(e, BVOr(IntLiteral(5), IntLiteral(4))) === IntLiteral(5)
    eval(e, BVOr(IntLiteral(5), IntLiteral(2))) === IntLiteral(7)

    eval(e, BVXor(IntLiteral(3), IntLiteral(1))) === IntLiteral(2)
    eval(e, BVXor(IntLiteral(3), IntLiteral(3))) === IntLiteral(0)

    eval(e, BVNot(IntLiteral(1))) === IntLiteral(-2)

    eval(e, BVShiftLeft(IntLiteral(3), IntLiteral(1))) === IntLiteral(6)
    eval(e, BVShiftLeft(IntLiteral(4), IntLiteral(2))) === IntLiteral(16)

    eval(e, BVLShiftRight(IntLiteral(8), IntLiteral(1))) === IntLiteral(4)
    eval(e, BVAShiftRight(IntLiteral(8), IntLiteral(1))) === IntLiteral(4)
  }

  test("Arithmetic") {
    val e = evaluator(ctx)

    eval(e, Plus(IntegerLiteral(3), IntegerLiteral(5)))  === IntegerLiteral(8)
    eval(e, Minus(IntegerLiteral(7), IntegerLiteral(2))) === IntegerLiteral(5)
    eval(e, UMinus(IntegerLiteral(7)))                   === IntegerLiteral(-7)
    eval(e, Times(IntegerLiteral(2), IntegerLiteral(3))) === IntegerLiteral(6)
  }

  test("BigInt Modulo and Remainder") {
    val e = evaluator(ctx)

    eval(e, Division(IntegerLiteral(10), IntegerLiteral(3)))   === IntegerLiteral(3)
    eval(e, Remainder(IntegerLiteral(10), IntegerLiteral(3)))  === IntegerLiteral(1)
    eval(e, Modulo(IntegerLiteral(10), IntegerLiteral(3)))     === IntegerLiteral(1)

    eval(e, Division(IntegerLiteral(-1), IntegerLiteral(3)))   === IntegerLiteral(0)
    eval(e, Remainder(IntegerLiteral(-1), IntegerLiteral(3)))  === IntegerLiteral(-1)

    eval(e, Modulo(IntegerLiteral(-1), IntegerLiteral(3)))     === IntegerLiteral(2)

    eval(e, Division(IntegerLiteral(-1), IntegerLiteral(-3)))  === IntegerLiteral(0)
    eval(e, Remainder(IntegerLiteral(-1), IntegerLiteral(-3))) === IntegerLiteral(-1)
    eval(e, Modulo(IntegerLiteral(-1), IntegerLiteral(-3)))    === IntegerLiteral(2)

    eval(e, Division(IntegerLiteral(1), IntegerLiteral(-3)))   === IntegerLiteral(0)
    eval(e, Remainder(IntegerLiteral(1), IntegerLiteral(-3)))  === IntegerLiteral(1)
    eval(e, Modulo(IntegerLiteral(1), IntegerLiteral(-3)))     === IntegerLiteral(1)
  }

  test("Int Comparisons") {
    val e = evaluator(ctx)

    eval(e, GreaterEquals(IntegerLiteral(7), IntegerLiteral(4)))  === BooleanLiteral(true)
    eval(e, GreaterEquals(IntegerLiteral(7), IntegerLiteral(7)))  === BooleanLiteral(true)
    eval(e, GreaterEquals(IntegerLiteral(4), IntegerLiteral(7)))  === BooleanLiteral(false)

    eval(e, GreaterThan(IntegerLiteral(7), IntegerLiteral(4)))    === BooleanLiteral(true)
    eval(e, GreaterThan(IntegerLiteral(7), IntegerLiteral(7)))    === BooleanLiteral(false)
    eval(e, GreaterThan(IntegerLiteral(4), IntegerLiteral(7)))    === BooleanLiteral(false)

    eval(e, LessEquals(IntegerLiteral(7), IntegerLiteral(4)))     === BooleanLiteral(false)
    eval(e, LessEquals(IntegerLiteral(7), IntegerLiteral(7)))     === BooleanLiteral(true)
    eval(e, LessEquals(IntegerLiteral(4), IntegerLiteral(7)))     === BooleanLiteral(true)

    eval(e, LessThan(IntegerLiteral(7), IntegerLiteral(4)))       === BooleanLiteral(false)
    eval(e, LessThan(IntegerLiteral(7), IntegerLiteral(7)))       === BooleanLiteral(false)
    eval(e, LessThan(IntegerLiteral(4), IntegerLiteral(7)))       === BooleanLiteral(true)
  }

  test("Int Modulo and Remainder") {
    val e = evaluator(ctx)

    eval(e, Division(IntLiteral(10), IntLiteral(3)))    === IntLiteral(3)
    eval(e, Remainder(IntLiteral(10), IntLiteral(3)))   === IntLiteral(1)

    eval(e, Division(IntLiteral(-1), IntLiteral(3)))    === IntLiteral(0)
    eval(e, Remainder(IntLiteral(-1), IntLiteral(3)))   === IntLiteral(-1)

    eval(e, Division(IntLiteral(-1), IntLiteral(-3)))   === IntLiteral(0)
    eval(e, Remainder(IntLiteral(-1), IntLiteral(-3)))  === IntLiteral(-1)

    eval(e, Division(IntLiteral(1), IntLiteral(-3)))    === IntLiteral(0)
    eval(e, Remainder(IntLiteral(1), IntLiteral(-3)))   === IntLiteral(1)
  }

  test("Boolean Operations") {
    val e = evaluator(ctx)

    eval(e, And(BooleanLiteral(true), BooleanLiteral(true)))      === BooleanLiteral(true)
    eval(e, And(BooleanLiteral(true), BooleanLiteral(false)))     === BooleanLiteral(false)
    eval(e, And(BooleanLiteral(false), BooleanLiteral(false)))    === BooleanLiteral(false)
    eval(e, And(BooleanLiteral(false), BooleanLiteral(true)))     === BooleanLiteral(false)
    eval(e, Or(BooleanLiteral(true), BooleanLiteral(true)))       === BooleanLiteral(true)
    eval(e, Or(BooleanLiteral(true), BooleanLiteral(false)))      === BooleanLiteral(true)
    eval(e, Or(BooleanLiteral(false), BooleanLiteral(false)))     === BooleanLiteral(false)
    eval(e, Or(BooleanLiteral(false), BooleanLiteral(true)))      === BooleanLiteral(true)
    eval(e, Not(BooleanLiteral(false)))                           === BooleanLiteral(true)
    eval(e, Not(BooleanLiteral(true)))                            === BooleanLiteral(false)
  }

  test("Real Arightmetic") {
    val e = evaluator(ctx)

    eval(e, Plus(FractionLiteral(2, 3), FractionLiteral(1, 3))) === FractionLiteral(1, 1)
    eval(e, Minus(FractionLiteral(1, 1), FractionLiteral(1, 4))) === FractionLiteral(3, 4)
    eval(e, UMinus(FractionLiteral(7, 1))) === FractionLiteral(-7, 1)
    eval(e, Times(FractionLiteral(2, 3), FractionLiteral(1, 3))) === FractionLiteral(2, 9)
  }

  test("Real Comparisons") {
    val e = evaluator(ctx)

    eval(e, GreaterEquals(FractionLiteral(7, 1), FractionLiteral(4, 2))) === BooleanLiteral(true)
    eval(e, GreaterEquals(FractionLiteral(7, 2), FractionLiteral(49, 13))) === BooleanLiteral(false)

    eval(e, GreaterThan(FractionLiteral(49, 13), FractionLiteral(7, 2))) === BooleanLiteral(true)
    eval(e, GreaterThan(FractionLiteral(49, 14), FractionLiteral(7, 2))) === BooleanLiteral(false)
    eval(e, GreaterThan(FractionLiteral(4, 2), FractionLiteral(7, 1))) === BooleanLiteral(false)

    eval(e, LessEquals(FractionLiteral(7, 1), FractionLiteral(4, 2))) === BooleanLiteral(false)
    eval(e, LessEquals(FractionLiteral(7, 2), FractionLiteral(49, 13))) === BooleanLiteral(true)

    eval(e, LessThan(FractionLiteral(49, 13), FractionLiteral(7, 2))) === BooleanLiteral(false)
    eval(e, LessThan(FractionLiteral(49, 14), FractionLiteral(7, 2))) === BooleanLiteral(false)
    eval(e, LessThan(FractionLiteral(4, 2), FractionLiteral(7, 1))) === BooleanLiteral(true)
  }

  test("Simple Variable") {
    val e = evaluator(ctx)

    val v = Variable.fresh("id", Int32Type)

    eval(e, v, Map(v.toVal -> IntLiteral(23))) === IntLiteral(23)
  }

  test("Undefined Variable") {
    val e = evaluator(ctx)

    val v1 = Variable.fresh("id", Int32Type)
    val v2 = Variable.fresh("foo", Int32Type)

    eval(e, v1, Map(v2.toVal -> IntLiteral(23))).failed
  }

  test("Let") {
    val e = evaluator(ctx)

    val v = Variable.fresh("id", Int32Type)
    eval(e, Let(v.toVal, IntLiteral(42), v)) === IntLiteral(42)
    eval(e, Let(v.toVal, IntLiteral(42), Plus(v, IntLiteral(1)))) === IntLiteral(43)
  }

  test("Map Operations") {
    val e = evaluator(ctx)

    eval(e, Equals(
      FiniteMap(Seq.empty, IntLiteral(12), Int32Type, Int32Type),
      FiniteMap(Seq.empty, IntLiteral(12), Int32Type, Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteMap(Seq.empty, IntLiteral(9), Int32Type, Int32Type),
      FiniteMap(Seq.empty, IntLiteral(12), Int32Type, Int32Type))
    ) === BooleanLiteral(false)

    eval(e, Equals(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(3)), IntLiteral(9), Int32Type, Int32Type),
      FiniteMap(Seq(IntLiteral(2) -> IntLiteral(3), IntLiteral(1) -> IntLiteral(2)), IntLiteral(9), Int32Type, Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(1) -> IntLiteral(3)), IntLiteral(9), Int32Type, Int32Type),
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(3), IntLiteral(1) -> IntLiteral(2)), IntLiteral(9), Int32Type, Int32Type))
    ) === BooleanLiteral(false)

    eval(e, Equals(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(1) -> IntLiteral(3)), IntLiteral(9), Int32Type, Int32Type),
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(3)), IntLiteral(9), Int32Type, Int32Type))
    ) === BooleanLiteral(true)

    eval(e, MapApply(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(4)), IntLiteral(6), Int32Type, Int32Type),
      IntLiteral(1))
    ) === IntLiteral(2)

    eval(e, MapApply(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(4)), IntLiteral(6), Int32Type, Int32Type),
      IntLiteral(3))
    ) === IntLiteral(6)

    eval(e, MapApply(
      MapUpdated(
        FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(4)), IntLiteral(6), Int32Type, Int32Type),
        IntLiteral(1), IntLiteral(3)),
      IntLiteral(1))
    ) === IntLiteral(3)
  }

  test("Map with variables") {
    val e = evaluator(ctx)

    val v1 = Variable.fresh("v1", Int32Type)
    val v2 = Variable.fresh("v2", Int32Type)
    val v3 = Variable.fresh("v3", Int32Type)

    eval(e, Equals(
      FiniteMap(Seq(v1 -> IntLiteral(2), v2 -> IntLiteral(4)), v3, Int32Type, Int32Type),
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(4)), IntLiteral(6), Int32Type, Int32Type)),
      Map(v1.toVal -> IntLiteral(1), v2.toVal -> IntLiteral(2), v3.toVal -> IntLiteral(6))
    ) === BooleanLiteral(true)

    eval(e, MapApply(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(4)), IntLiteral(6), Int32Type, Int32Type),
      v1),
      Map(v1.toVal -> IntLiteral(3))
    ) === IntLiteral(6)

    eval(e, MapApply(
      MapUpdated(
        FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(4)), IntLiteral(6), Int32Type, Int32Type),
        v1, v2), v3),
      Map(v1.toVal -> IntLiteral(1), v2.toVal -> IntLiteral(3), v3.toVal -> IntLiteral(1))
    ) === IntLiteral(3)
  }

  test("Nested lambdas") {
    val e = evaluator(ctx)

    val ap = ValDef(FreshIdentifier("a"), StringType, Set())
    val bp = ValDef(FreshIdentifier("b"), StringType, Set())

    val body = Application(Application(
      Lambda(
        Seq(ap),
        Lambda(
          Seq(bp),
          StringConcat(StringConcat(ap.toVariable, StringLiteral(":")), bp.toVariable))
        ),
      Seq(StringLiteral("Winner"))
    ), Seq(StringLiteral("Mikael")))

    eval(e, Equals(body, StringLiteral("Winner:Mikael"))) === BooleanLiteral(true)
  }

  abstract class EvalDSL {
    def res: Expr
    def ===(res: Expr): Unit
    def failed: Unit = {}
    def success: Expr = res
  }

  case class Success(expr: Expr, env: Map[ValDef, Expr], evaluator: DeterministicEvaluator, res: Expr) extends EvalDSL {
    override def failed = {
      fail(s"Evaluation of '$expr' with '$evaluator' (and env $env) should have failed")
    }

    def ===(exp: Expr) = {
      assert(res === exp)
    }
  }

  case class Failed(expr: Expr, env: Map[ValDef, Expr], evaluator: DeterministicEvaluator, err: String) extends EvalDSL {
    override def success = {
      fail(s"Evaluation of '$expr' with '$evaluator' (and env $env) should have succeeded but failed with $err")
    }

    def res = success

    def ===(res: Expr) = success
  }

  def eval(
    e: DeterministicEvaluator { val program: InoxProgram },
    toEval: Expr,
    env: Map[ValDef, Expr] = Map()
  ): EvalDSL = {
    e.eval(toEval, Model(e.program)(env, Map.empty)) match {
      case EvaluationResults.Successful(res)     => Success(toEval, env, e, res)
      case EvaluationResults.RuntimeError(err)   => Failed(toEval, env, e, err)
      case EvaluationResults.EvaluatorError(err) => Failed(toEval, env, e, err)
    }
  }
}
