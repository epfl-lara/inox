/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import org.scalatest._

class SemanticsSuite extends FunSuite {
  import inox.trees._
  import SolverResponses._

  implicit val symbols = new Symbols(Map.empty, Map.empty)
  val solverNames: Seq[String] = {
    (if (SolverFactory.hasNativeZ3) Seq("nativez3", "unrollz3") else Nil) ++
    (if (SolverFactory.hasZ3) Seq("smt-z3") else Nil) ++
    (if (SolverFactory.hasCVC4) Seq("smt-cvc4") else Nil) ++
    Seq("princess")
  }

  def solver(ctx: Context): SimpleSolverAPI { val factory: SolverFactory { val program: InoxProgram } } = {
    val program = InoxProgram(ctx, symbols)
    SimpleSolverAPI(SolverFactory.default(program))
  }

  protected def test(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    test(name, _ => true, tags : _*)(body)
  }

  protected def test(name: String, filter: Context => Boolean, tags: Tag*)(body: Context => Unit): Unit = {
    for {
      sname <- solverNames
      ctx = TestContext(Options(Seq(optSelectedSolvers(Set(sname)))))
      if filter(ctx)
    } super.test(s"$name solver=$sname", tags : _*)(body(ctx))
  }

  protected def filterPrincess(ctx: Context): Boolean = {
    ctx.options.findOptionOrDefault(optSelectedSolvers) != Set("princess")
  }

  protected def check(s: SimpleSolverAPI { val factory: SolverFactory { val program: InoxProgram } }, e: Expr, expected: Expr) = {
    val v = Variable(FreshIdentifier("v"), e.getType)
    s.solveSAT(Equals(v, e)) match {
      case SatWithModel(model) => assert(model.get(v.toVal) == Some(expected))
      case _ => fail(s"Solving of '$e' failed.")
    }
  }

  test("Literals") { ctx =>
    val s = solver(ctx)

    check(s, BooleanLiteral(true),   BooleanLiteral(true))
    check(s, BooleanLiteral(false),  BooleanLiteral(false))
    check(s, IntLiteral(0),          IntLiteral(0))
    check(s, IntLiteral(42),         IntLiteral(42))
    check(s, UnitLiteral(),          UnitLiteral())
    check(s, IntegerLiteral(0),      IntegerLiteral(0))
    check(s, IntegerLiteral(42),     IntegerLiteral(42))
    check(s, FractionLiteral(0 ,1),  FractionLiteral(0 ,1))
    check(s, FractionLiteral(42 ,1), FractionLiteral(42, 1))
    check(s, FractionLiteral(26, 3), FractionLiteral(26, 3))
  }

  test("BitVector Arithmetic") { ctx =>
    val s = solver(ctx)

    check(s, Plus(IntLiteral(3), IntLiteral(5)),            IntLiteral(8))
    check(s, Plus(IntLiteral(0), IntLiteral(5)),            IntLiteral(5))
    check(s, Plus(IntLiteral(1), IntLiteral(-2)),           IntLiteral(-1))
    check(s, Plus(IntLiteral(Int.MaxValue), IntLiteral(1)), IntLiteral(Int.MinValue))
    check(s, Times(IntLiteral(3), IntLiteral(3)),           IntLiteral(9))
  }

  test("solve bitwise operations", filterPrincess _) { ctx =>
    val s = solver(ctx)

    check(s, BVAnd(IntLiteral(3), IntLiteral(1)), IntLiteral(1))
    check(s, BVAnd(IntLiteral(3), IntLiteral(3)), IntLiteral(3))
    check(s, BVAnd(IntLiteral(5), IntLiteral(3)), IntLiteral(1))
    check(s, BVAnd(IntLiteral(5), IntLiteral(4)), IntLiteral(4))
    check(s, BVAnd(IntLiteral(5), IntLiteral(2)), IntLiteral(0))

    check(s, BVOr(IntLiteral(3), IntLiteral(1)), IntLiteral(3))
    check(s, BVOr(IntLiteral(3), IntLiteral(3)), IntLiteral(3))
    check(s, BVOr(IntLiteral(5), IntLiteral(3)), IntLiteral(7))
    check(s, BVOr(IntLiteral(5), IntLiteral(4)), IntLiteral(5))
    check(s, BVOr(IntLiteral(5), IntLiteral(2)), IntLiteral(7))

    check(s, BVXor(IntLiteral(3), IntLiteral(1)), IntLiteral(2))
    check(s, BVXor(IntLiteral(3), IntLiteral(3)), IntLiteral(0))

    check(s, BVNot(IntLiteral(1)), IntLiteral(-2))

    check(s, BVShiftLeft(IntLiteral(3), IntLiteral(1)), IntLiteral(6))
    check(s, BVShiftLeft(IntLiteral(4), IntLiteral(2)), IntLiteral(16))

    check(s, BVLShiftRight(IntLiteral(8), IntLiteral(1)), IntLiteral(4))
    check(s, BVAShiftRight(IntLiteral(8), IntLiteral(1)), IntLiteral(4))
  }

  test("Arithmetic") { ctx =>
    val s = solver(ctx)

    check(s, Plus(IntegerLiteral(3), IntegerLiteral(5)),  IntegerLiteral(8))
    check(s, Minus(IntegerLiteral(7), IntegerLiteral(2)), IntegerLiteral(5))
    check(s, UMinus(IntegerLiteral(7)),                   IntegerLiteral(-7))
    check(s, Times(IntegerLiteral(2), IntegerLiteral(3)), IntegerLiteral(6))
  }

  test("BigInt Modulo and Remainder") { ctx =>
    val s = solver(ctx)

    check(s, Division(IntegerLiteral(10), IntegerLiteral(3)),  IntegerLiteral(3))
    check(s, Remainder(IntegerLiteral(10), IntegerLiteral(3)), IntegerLiteral(1))
    check(s, Modulo(IntegerLiteral(10), IntegerLiteral(3)),    IntegerLiteral(1))

    check(s, Division(IntegerLiteral(-1), IntegerLiteral(3)),  IntegerLiteral(0))
    check(s, Remainder(IntegerLiteral(-1), IntegerLiteral(3)), IntegerLiteral(-1))

    check(s, Modulo(IntegerLiteral(-1), IntegerLiteral(3)),    IntegerLiteral(2))

    check(s, Division(IntegerLiteral(-1), IntegerLiteral(-3)), IntegerLiteral(0))
    check(s, Remainder(IntegerLiteral(-1), IntegerLiteral(-3)),IntegerLiteral(-1))
    check(s, Modulo(IntegerLiteral(-1), IntegerLiteral(-3)),   IntegerLiteral(2))

    check(s, Division(IntegerLiteral(1), IntegerLiteral(-3)),  IntegerLiteral(0))
    check(s, Remainder(IntegerLiteral(1), IntegerLiteral(-3)), IntegerLiteral(1))
    check(s, Modulo(IntegerLiteral(1), IntegerLiteral(-3)),    IntegerLiteral(1))
  }

  test("Int Comparisons") { ctx =>
    val s = solver(ctx)

    check(s, GreaterEquals(IntegerLiteral(7), IntegerLiteral(4)), BooleanLiteral(true))
    check(s, GreaterEquals(IntegerLiteral(7), IntegerLiteral(7)), BooleanLiteral(true))
    check(s, GreaterEquals(IntegerLiteral(4), IntegerLiteral(7)), BooleanLiteral(false))

    check(s, GreaterThan(IntegerLiteral(7), IntegerLiteral(4)),   BooleanLiteral(true))
    check(s, GreaterThan(IntegerLiteral(7), IntegerLiteral(7)),   BooleanLiteral(false))
    check(s, GreaterThan(IntegerLiteral(4), IntegerLiteral(7)),   BooleanLiteral(false))

    check(s, LessEquals(IntegerLiteral(7), IntegerLiteral(4)),    BooleanLiteral(false))
    check(s, LessEquals(IntegerLiteral(7), IntegerLiteral(7)),    BooleanLiteral(true))
    check(s, LessEquals(IntegerLiteral(4), IntegerLiteral(7)),    BooleanLiteral(true))

    check(s, LessThan(IntegerLiteral(7), IntegerLiteral(4)),      BooleanLiteral(false))
    check(s, LessThan(IntegerLiteral(7), IntegerLiteral(7)),      BooleanLiteral(false))
    check(s, LessThan(IntegerLiteral(4), IntegerLiteral(7)),      BooleanLiteral(true))
  }

  test("Int Modulo and Remainder", filterPrincess _) { ctx =>
    val s = solver(ctx)

    check(s, Division(IntLiteral(10), IntLiteral(3)),   IntLiteral(3))
    check(s, Remainder(IntLiteral(10), IntLiteral(3)),  IntLiteral(1))

    check(s, Division(IntLiteral(-1), IntLiteral(3)),   IntLiteral(0))
    check(s, Remainder(IntLiteral(-1), IntLiteral(3)),  IntLiteral(-1))

    check(s, Division(IntLiteral(-1), IntLiteral(-3)),  IntLiteral(0))
    check(s, Remainder(IntLiteral(-1), IntLiteral(-3)), IntLiteral(-1))

    check(s, Division(IntLiteral(1), IntLiteral(-3)),   IntLiteral(0))
    check(s, Remainder(IntLiteral(1), IntLiteral(-3)),  IntLiteral(1))
  }

  test("Boolean Operations") { ctx =>
    val s = solver(ctx)

    check(s, And(BooleanLiteral(true), BooleanLiteral(true)),   BooleanLiteral(true))
    check(s, And(BooleanLiteral(true), BooleanLiteral(false)),  BooleanLiteral(false))
    check(s, And(BooleanLiteral(false), BooleanLiteral(false)), BooleanLiteral(false))
    check(s, And(BooleanLiteral(false), BooleanLiteral(true)),  BooleanLiteral(false))
    check(s, Or(BooleanLiteral(true), BooleanLiteral(true)),    BooleanLiteral(true))
    check(s, Or(BooleanLiteral(true), BooleanLiteral(false)),   BooleanLiteral(true))
    check(s, Or(BooleanLiteral(false), BooleanLiteral(false)),  BooleanLiteral(false))
    check(s, Or(BooleanLiteral(false), BooleanLiteral(true)),   BooleanLiteral(true))
    check(s, Not(BooleanLiteral(false)),                        BooleanLiteral(true))
    check(s, Not(BooleanLiteral(true)),                         BooleanLiteral(false))
  }

  test("Real Arightmetic") { ctx =>
    val s = solver(ctx)

    check(s, Plus(FractionLiteral(2, 3), FractionLiteral(1, 3)),  FractionLiteral(1, 1))
    check(s, Minus(FractionLiteral(1, 1), FractionLiteral(1, 4)), FractionLiteral(3, 4))
    check(s, UMinus(FractionLiteral(7, 1)),                       FractionLiteral(-7, 1))
    check(s, Times(FractionLiteral(2, 3), FractionLiteral(1, 3)), FractionLiteral(2, 9))
  }

  test("Real Comparisons") { ctx =>
    val s = solver(ctx)

    check(s, GreaterEquals(FractionLiteral(7, 1), FractionLiteral(4, 2)),   BooleanLiteral(true))
    check(s, GreaterEquals(FractionLiteral(7, 2), FractionLiteral(49, 13)), BooleanLiteral(false))

    check(s, GreaterThan(FractionLiteral(49, 13), FractionLiteral(7, 2)),   BooleanLiteral(true))
    check(s, GreaterThan(FractionLiteral(49, 14), FractionLiteral(7, 2)),   BooleanLiteral(false))
    check(s, GreaterThan(FractionLiteral(4, 2), FractionLiteral(7, 1)),     BooleanLiteral(false))

    check(s, LessEquals(FractionLiteral(7, 1), FractionLiteral(4, 2)),      BooleanLiteral(false))
    check(s, LessEquals(FractionLiteral(7, 2), FractionLiteral(49, 13)),    BooleanLiteral(true))

    check(s, LessThan(FractionLiteral(49, 13), FractionLiteral(7, 2)),      BooleanLiteral(false))
    check(s, LessThan(FractionLiteral(49, 14), FractionLiteral(7, 2)),      BooleanLiteral(false))
    check(s, LessThan(FractionLiteral(4, 2), FractionLiteral(7, 1)),        BooleanLiteral(true))
  }

  test("Let") { ctx =>
    val s = solver(ctx)

    val v = Variable(FreshIdentifier("id"), Int32Type)
    check(s, Let(v.toVal, IntLiteral(42), v), IntLiteral(42))
    check(s, Let(v.toVal, IntLiteral(42), Plus(v, IntLiteral(1))), IntLiteral(43))
  }

  test("Map Operations", filterPrincess _) { ctx =>
    val s = solver(ctx)

    check(s, Equals(
      FiniteMap(Seq.empty, IntLiteral(12), Int32Type, Int32Type),
      FiniteMap(Seq.empty, IntLiteral(12), Int32Type, Int32Type)
    ), BooleanLiteral(true))

    check(s, Equals(
      FiniteMap(Seq.empty, IntLiteral(9), Int32Type, Int32Type),
      FiniteMap(Seq.empty, IntLiteral(12), Int32Type, Int32Type)
    ), BooleanLiteral(false))

    check(s, Equals(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(3)), IntLiteral(9), Int32Type, Int32Type),
      FiniteMap(Seq(IntLiteral(2) -> IntLiteral(3), IntLiteral(1) -> IntLiteral(2)), IntLiteral(9), Int32Type, Int32Type)
    ), BooleanLiteral(true))

    check(s, Equals(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(1) -> IntLiteral(3)), IntLiteral(9), Int32Type, Int32Type),
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(3), IntLiteral(1) -> IntLiteral(2)), IntLiteral(9), Int32Type, Int32Type)
    ), BooleanLiteral(false))

    check(s, Equals(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(1) -> IntLiteral(3)), IntLiteral(9), Int32Type, Int32Type),
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(3)), IntLiteral(9), Int32Type, Int32Type)
    ), BooleanLiteral(true))

    check(s, MapApply(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(4)), IntLiteral(6), Int32Type, Int32Type),
      IntLiteral(1)
    ), IntLiteral(2))

    check(s, MapApply(
      FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(4)), IntLiteral(6), Int32Type, Int32Type),
      IntLiteral(3)
    ), IntLiteral(6))

    check(s, MapApply(
      MapUpdated(
        FiniteMap(Seq(IntLiteral(1) -> IntLiteral(2), IntLiteral(2) -> IntLiteral(4)), IntLiteral(6), Int32Type, Int32Type),
        IntLiteral(1), IntLiteral(3)),
      IntLiteral(1)
    ), IntLiteral(3))
  }
}
