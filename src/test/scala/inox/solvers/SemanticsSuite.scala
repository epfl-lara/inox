/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.Tag

class SemanticsSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  given symbols: Symbols = NoSymbols
  val program = InoxProgram(symbols)

  val solverNames: Seq[String] = {
    (if (SolverFactory.hasNativeZ3) Seq("nativez3", "unrollz3") else Nil) ++
    (if (SolverFactory.hasZ3) Seq("smt-z3") else Nil) ++
    (if (SolverFactory.hasCVC4) Seq("smt-cvc4") else Nil) ++
    (if (SolverFactory.hasCVC5) Seq("smt-cvc5") else Nil) ++
    Seq("princess")
  }

  def solver(ctx: Context): SimpleSolverAPI { val program: InoxProgram } = {
    SimpleSolverAPI(program.getSolver(ctx))
  }

  protected def test(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    test(name, _ => true, tags*)(body)
  }

  protected def test(name: String, filter: Context => Boolean, tags: Tag*)(body: Context => Unit): Unit = {
    // Workaround for a compiler crash caused by calling super.test
    def superTest(self: AnyFunSuite, name: String)(body: => Unit): Unit =
      self.test(name, tags*)(body)

    for {
      sname <- solverNames
      ctx = TestContext(Options(Seq(optSelectedSolvers(Set(sname)))))
      if filter(ctx)
    } superTest(this, s"$name solver=$sname")(body(ctx))
  }

  protected def filterSolvers(ctx: Context, princess: Boolean = false, cvc4: Boolean = false, cvc5: Boolean = false, unroll: Boolean = false, z3: Boolean = false, native: Boolean = false): Boolean = {
    val solvers = ctx.options.findOptionOrDefault(optSelectedSolvers)
    (!princess || solvers != Set("princess")) &&
    (!unroll || solvers != Set("unrollz3")) &&
    (!z3 || solvers != Set("smt-z3")) &&
    (!native || solvers != Set("nativez3")) &&
    (!cvc4 || solvers != Set("smt-cvc4")) &&
    (!cvc5 || solvers != Set("smt-cvc5"))
  }

  protected def check(s: SimpleSolverAPI { val program: InoxProgram }, e: Expr, expected: Expr) = {
    val v = Variable.fresh("v", e.getType)
    s.solveSAT(Equals(v, e)) match {
      case SatWithModel(model) => assert(model.vars.get(v.toVal) == Some(expected))
      case got => fail(s"Solving of '$e' failed with $got.")
    }
  }

  test("Literals") { ctx =>
    val s = solver(ctx)

    check(s, BooleanLiteral(true),   BooleanLiteral(true))
    check(s, BooleanLiteral(false),  BooleanLiteral(false))
    check(s, Int8Literal(-1),        Int8Literal(-1))
    check(s, Int8Literal(0),         Int8Literal(0))
    check(s, Int8Literal(58),        Int8Literal(58))
    check(s, Int16Literal(58),       Int16Literal(58))
    check(s, Int16Literal(-1),       Int16Literal(-1))
    check(s, Int16Literal(0),        Int16Literal(0))
    check(s, Int32Literal(-1),       Int32Literal(-1))
    check(s, Int32Literal(0),        Int32Literal(0))
    check(s, Int32Literal(42),       Int32Literal(42))
    check(s, UnitLiteral(),          UnitLiteral())
    check(s, IntegerLiteral(-1),     IntegerLiteral(-1))
    check(s, IntegerLiteral(0),      IntegerLiteral(0))
    check(s, IntegerLiteral(42),     IntegerLiteral(42))
    check(s, FractionLiteral(0, 1),  FractionLiteral(0, 1))
    check(s, FractionLiteral(42 ,1), FractionLiteral(42, 1))
    check(s, FractionLiteral(26, 3), FractionLiteral(26, 3))
  }

  test("BitVector & Large integer Literals", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    // Test the literals that princess doesn't support.
    check(s, BVLiteral(true, 0, 13),           BVLiteral(true, 0, 13))
    check(s, BVLiteral(true, -1, 13),          BVLiteral(true, -1, 13))
    check(s, BVLiteral(true, -1, 33),          BVLiteral(true, -1, 33))
    check(s, BVLiteral(true, 4294967296L, 33), BVLiteral(true, 4294967296L, 33)) // 2^32 fits in 33 bits!
    check(s, Int64Literal(-1),           Int64Literal(-1))
    check(s, Int64Literal(4294967296L),  Int64Literal(4294967296L))

    check(s, IntegerLiteral(1099511627776L), IntegerLiteral(1099511627776L)) // 2^40
  }

  test("BitVector Arithmetic") { ctx =>
    val s = solver(ctx)

    check(s, Plus(Int8Literal(3), Int8Literal(5)),              Int8Literal(8))
    check(s, Plus(Int8Literal(Byte.MaxValue), Int8Literal(1)),  Int8Literal(Byte.MinValue))
    check(s, Times(Int8Literal(3), Int8Literal(3)),             Int8Literal(9))

    check(s, Plus(Int32Literal(3), Int32Literal(5)),            Int32Literal(8))
    check(s, Plus(Int32Literal(0), Int32Literal(5)),            Int32Literal(5))
    check(s, Plus(Int32Literal(1), Int32Literal(-2)),           Int32Literal(-1))
    check(s, Plus(Int32Literal(Int.MaxValue), Int32Literal(1)), Int32Literal(Int.MinValue))
    check(s, Times(Int32Literal(3), Int32Literal(3)),           Int32Literal(9))
  }

  test("BitVector Arithmetic Bis", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    check(s, Plus(BVLiteral(true, 3, 13), BVLiteral(true, 5, 13)),              BVLiteral(true, 8, 13))
    check(s, Plus(BVLiteral(true, 3, 16), BVLiteral(true, 5, 16)),              BVLiteral(true, 8, 16))
    check(s, Plus(BVLiteral(false, 3, 13), BVLiteral(false, 5, 13)),            BVLiteral(false, 8, 13))
    check(s, Plus(BVLiteral(false, 3, 16), BVLiteral(false, 5, 16)),            BVLiteral(false, 8, 16))
    check(s, Plus(BVLiteral(true, Short.MaxValue, 16), BVLiteral(true, 1, 16)), BVLiteral(true, Short.MinValue, 16))
    check(s, Plus(BVLiteral(false, Short.MaxValue, 16), BVLiteral(false, 1, 16)), BVLiteral(false, BigInt(Short.MaxValue) + 1, 16))
  }

  test("BitVector Casts", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)
    val b: Byte = 1

    check(s, BVWideningCast(Int8Literal(0), Int32Type()),             Int32Literal(0))
    check(s, BVWideningCast(Int8Literal(1), Int32Type()),             Int32Literal(1))
    check(s, BVWideningCast(BVLiteral(true, 2, 3), BVType(true, 4)),  BVLiteral(true, 2, 4))
    check(s, BVWideningCast(Int8Literal(1), BVType(true, 9)),         BVLiteral(true, 1, 9))
    check(s, BVWideningCast(BVLiteral(true, 1, 2), Int32Type()),      Int32Literal(1))
    check(s, BVWideningCast(BVLiteral(true, 1, 1), Int32Type()),      Int32Literal(-1)) // 2's complement on 1 bit
    check(s, BVWideningCast(Int8Literal(-1), Int32Type()),            Int32Literal(-1))
    check(s, BVWideningCast(Int8Literal(-128), Int32Type()),          Int32Literal(-128))

    check(s, BVNarrowingCast(Int8Literal(1), BVType(true, 7)),        BVLiteral(true, 1, 7))
    check(s, BVNarrowingCast(Int32Literal(1), Int8Type()),            Int8Literal(1))
    check(s, BVNarrowingCast(BVLiteral(true, 1, 33), Int32Type()),    Int32Literal(1))
    check(s, BVNarrowingCast(Int32Literal(-1), Int8Type()),           Int8Literal(-1))
    check(s, BVNarrowingCast(Int32Literal(-128), Int8Type()),         Int8Literal(-128))
    check(s, BVNarrowingCast(Int32Literal(-129), Int8Type()),         Int8Literal(127))
    check(s, BVNarrowingCast(Int32Literal(128), Int8Type()),          Int8Literal(-128))

    check(s, Plus(Int32Literal(1), BVWideningCast(Int8Literal(1), Int32Type())), Int32Literal(2))

    check(s, Plus(
              BVWideningCast(Int32Literal(Int.MaxValue), Int64Type()),
              BVWideningCast(Int8Literal(1), Int64Type())
            ), Int64Literal(Int.MaxValue + b.toLong))

    check(s, Equals(Plus(
              BVWideningCast(Int32Literal(Int.MaxValue), Int64Type()),
              BVWideningCast(Int8Literal(1), Int64Type())
            ), Int64Literal(Int.MaxValue + b.toInt)), BooleanLiteral(false)) // mind the `toInt` instead of `toLong`
  }


  test("solve bitwise operations", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    check(s, BVAnd(Int8Literal(3), Int8Literal(1)),         Int8Literal(1))
    check(s, BVOr(Int8Literal(5), Int8Literal(3)),          Int8Literal(7))
    check(s, BVXor(Int8Literal(3), Int8Literal(1)),         Int8Literal(2))
    check(s, BVNot(Int8Literal(1)),                         Int8Literal(-2))
    check(s, BVShiftLeft(Int8Literal(3), Int8Literal(1)),   Int8Literal(6))
    check(s, BVAShiftRight(Int8Literal(8), Int8Literal(1)), Int8Literal(4))

    check(s, BVAnd(Int32Literal(3), Int32Literal(1)), Int32Literal(1))
    check(s, BVAnd(Int32Literal(3), Int32Literal(3)), Int32Literal(3))
    check(s, BVAnd(Int32Literal(5), Int32Literal(3)), Int32Literal(1))
    check(s, BVAnd(Int32Literal(5), Int32Literal(4)), Int32Literal(4))
    check(s, BVAnd(Int32Literal(5), Int32Literal(2)), Int32Literal(0))

    check(s, BVOr(Int32Literal(3), Int32Literal(1)), Int32Literal(3))
    check(s, BVOr(Int32Literal(3), Int32Literal(3)), Int32Literal(3))
    check(s, BVOr(Int32Literal(5), Int32Literal(3)), Int32Literal(7))
    check(s, BVOr(Int32Literal(5), Int32Literal(4)), Int32Literal(5))
    check(s, BVOr(Int32Literal(5), Int32Literal(2)), Int32Literal(7))

    check(s, BVXor(Int32Literal(3), Int32Literal(1)), Int32Literal(2))
    check(s, BVXor(Int32Literal(3), Int32Literal(3)), Int32Literal(0))

    check(s, BVNot(Int32Literal(1)), Int32Literal(-2))

    check(s, BVShiftLeft(Int32Literal(3), Int32Literal(1)), Int32Literal(6))
    check(s, BVShiftLeft(Int32Literal(4), Int32Literal(2)), Int32Literal(16))

    check(s, BVLShiftRight(Int32Literal(8), Int32Literal(1)), Int32Literal(4))
    check(s, BVAShiftRight(Int32Literal(8), Int32Literal(1)), Int32Literal(4))

    check(s, BVNarrowingCast(
              BVAnd(BVWideningCast(Int8Literal(1), Int32Type()),
                    BVWideningCast(Int8Literal(2), Int32Type())),
              Int8Type()
            ), Int8Literal(0))

    def bvl(x: BigInt) = BVLiteral(true, x, 11)
    check(s, BVAnd(bvl(3), bvl(1)),          bvl(1))
    check(s, BVOr(bvl(5), bvl(3)),           bvl(7))
    check(s, BVXor(bvl(3), bvl(1)),          bvl(2))
    check(s, BVNot(bvl(1)),                  bvl(-2))
    check(s, BVShiftLeft(bvl(3), bvl(1)),    bvl(6))
    check(s, BVAShiftRight(bvl(8), bvl(1)),  bvl(4))

    def ubvl(x: BigInt) = BVLiteral(false, x, 11)
    check(s, BVAnd(bvl(3), bvl(1)),          bvl(1))
    check(s, BVOr(bvl(5), bvl(3)),           bvl(7))
    check(s, BVXor(bvl(3), bvl(1)),          bvl(2))
    check(s, BVNot(bvl(1)),                  bvl(2046))
    check(s, BVShiftLeft(bvl(3), bvl(1)),    bvl(6))
    check(s, BVAShiftRight(bvl(8), bvl(1)),  bvl(4))
  }

  test("BigInt Arithmetic") { ctx =>
    val s = solver(ctx)

    check(s, Plus(IntegerLiteral(3), IntegerLiteral(5)),  IntegerLiteral(8))
    check(s, Minus(IntegerLiteral(7), IntegerLiteral(2)), IntegerLiteral(5))
    check(s, UMinus(IntegerLiteral(7)),                   IntegerLiteral(-7))
    check(s, Times(IntegerLiteral(2), IntegerLiteral(3)), IntegerLiteral(6))
  }

  test("BigInt Division, Modulo and Remainder") { ctx =>
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

  test("BigInt Comparisons") { ctx =>
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

  test("BitVector Comparisons", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    check(s, GreaterEquals(Int8Literal(7), Int8Literal(4)),   BooleanLiteral(true))
    check(s, GreaterThan(Int8Literal(7), Int8Literal(7)),     BooleanLiteral(false))
    check(s, LessEquals(Int8Literal(4), Int8Literal(7)),      BooleanLiteral(true))
    check(s, LessThan(Int8Literal(4), Int8Literal(7)),        BooleanLiteral(true))

    check(s, GreaterEquals(Int16Literal(7), Int16Literal(4)), BooleanLiteral(true))
    check(s, GreaterThan(Int16Literal(7), Int16Literal(7)),   BooleanLiteral(false))
    check(s, LessEquals(Int16Literal(4), Int16Literal(7)),    BooleanLiteral(true))
    check(s, LessThan(Int16Literal(4), Int16Literal(7)),      BooleanLiteral(true))

    check(s, GreaterEquals(Int64Literal(7), Int64Literal(4)), BooleanLiteral(true))
    check(s, GreaterThan(Int64Literal(7), Int64Literal(7)),   BooleanLiteral(false))
    check(s, LessEquals(Int64Literal(4), Int64Literal(7)),    BooleanLiteral(true))
    check(s, LessThan(Int64Literal(4), Int64Literal(7)),      BooleanLiteral(true))

    check(s, GreaterEquals(Int32Literal(7), Int32Literal(4)), BooleanLiteral(true))
    check(s, GreaterEquals(Int32Literal(7), Int32Literal(7)), BooleanLiteral(true))
    check(s, GreaterEquals(Int32Literal(4), Int32Literal(7)), BooleanLiteral(false))

    check(s, GreaterThan(Int32Literal(7), Int32Literal(4)),   BooleanLiteral(true))
    check(s, GreaterThan(Int32Literal(7), Int32Literal(7)),   BooleanLiteral(false))
    check(s, GreaterThan(Int32Literal(4), Int32Literal(7)),   BooleanLiteral(false))

    check(s, LessEquals(Int32Literal(7), Int32Literal(4)),    BooleanLiteral(false))
    check(s, LessEquals(Int32Literal(7), Int32Literal(7)),    BooleanLiteral(true))
    check(s, LessEquals(Int32Literal(4), Int32Literal(7)),    BooleanLiteral(true))

    check(s, LessThan(Int32Literal(7), Int32Literal(4)),      BooleanLiteral(false))
    check(s, LessThan(Int32Literal(7), Int32Literal(7)),      BooleanLiteral(false))
    check(s, LessThan(Int32Literal(4), Int32Literal(7)),      BooleanLiteral(true))

    def bvl(x: BigInt) = BVLiteral(true, x, 13)
    check(s, GreaterEquals(bvl(7), bvl(4)), BooleanLiteral(true))
    check(s, GreaterThan(bvl(7), bvl(7)),   BooleanLiteral(false))
    check(s, LessEquals(bvl(7), bvl(7)),    BooleanLiteral(true))
    check(s, LessThan(bvl(4), bvl(7)),      BooleanLiteral(true))

    def ubvl(x: BigInt) = BVLiteral(false, x, 13)
    check(s, GreaterEquals(ubvl(7), ubvl(4)), BooleanLiteral(true))
    check(s, GreaterThan(ubvl(7), ubvl(7)),   BooleanLiteral(false))
    check(s, LessEquals(ubvl(7), ubvl(7)),    BooleanLiteral(true))
    check(s, LessThan(ubvl(4), ubvl(7)),      BooleanLiteral(true))
  }

  test("BitVector Division, Remainder and Modulo", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    check(s, Division(Int32Literal(10), Int32Literal(3)),   Int32Literal(3))
    check(s, Remainder(Int32Literal(10), Int32Literal(3)),  Int32Literal(1))
    check(s, Modulo(Int32Literal(10), Int32Literal(3)),     Int32Literal(1))

    check(s, Division(Int32Literal(-1), Int32Literal(3)),   Int32Literal(0))
    check(s, Remainder(Int32Literal(-1), Int32Literal(3)),  Int32Literal(-1))
    check(s, Modulo(Int32Literal(-1), Int32Literal(3)),     Int32Literal(2))

    check(s, Division(Int32Literal(-1), Int32Literal(-3)),  Int32Literal(0))
    check(s, Remainder(Int32Literal(-1), Int32Literal(-3)), Int32Literal(-1))
    check(s, Modulo(Int32Literal(-1), Int32Literal(-3)),    Int32Literal(2))

    check(s, Division(Int32Literal(1), Int32Literal(-3)),   Int32Literal(0))
    check(s, Remainder(Int32Literal(1), Int32Literal(-3)),  Int32Literal(1))
    check(s, Modulo(Int32Literal(1), Int32Literal(-3)),     Int32Literal(1))

    check(s, Division(Int8Literal(1), Int8Literal(-3)),     Int8Literal(0))
    check(s, Remainder(Int8Literal(1), Int8Literal(-3)),    Int8Literal(1))
    check(s, Remainder(Int8Literal(-1), Int8Literal(3)),    Int8Literal(-1))
    check(s, Modulo(Int8Literal(-1), Int8Literal(3)),       Int8Literal(2))
    check(s, Division(Int16Literal(1), Int16Literal(-3)),   Int16Literal(0))
    check(s, Remainder(Int16Literal(1), Int16Literal(-3)),  Int16Literal(1))
    check(s, Remainder(Int16Literal(-1), Int16Literal(3)),  Int16Literal(-1))
    check(s, Modulo(Int16Literal(-1), Int16Literal(3)),     Int16Literal(2))
    check(s, Division(Int64Literal(1), Int64Literal(-3)),   Int64Literal(0))
    check(s, Remainder(Int64Literal(1), Int64Literal(-3)),  Int64Literal(1))
    check(s, Remainder(Int64Literal(-1), Int64Literal(3)),  Int64Literal(-1))
    check(s, Modulo(Int64Literal(-1), Int64Literal(3)),     Int64Literal(2))

    def bvl(x: BigInt) = BVLiteral(true, x, 13)
    check(s, Division(bvl(1), bvl(-3)),  bvl(0))
    check(s, Remainder(bvl(1), bvl(-3)), bvl(1))
    check(s, Remainder(bvl(-1), bvl(3)), bvl(-1))
    check(s, Modulo(bvl(-1), bvl(3)),    bvl(2))

    def ubvl(x: BigInt) = BVLiteral(false, x, 13)
    check(s, Division(ubvl(1), ubvl(3)),  ubvl(0))
    check(s, Remainder(ubvl(1), ubvl(3)), ubvl(1))
    check(s, Modulo(ubvl(8191), ubvl(3)), ubvl(1))
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

  test("Real Arithmetic") { ctx =>
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

  import scala.collection.immutable.HashSet
  val floatValues: Set[Float] = HashSet(0f, -0f, 0.1f, -6.7f, Float.NaN, Float.MinValue, Float.MinValue, Float.PositiveInfinity, Float.NegativeInfinity)
  val doubleValues: Set[Double] = HashSet(0d, -0d, 0.1d, -6.7d, Double.NaN, Double.MinValue, Double.MinValue, Double.PositiveInfinity, Double.NegativeInfinity)


  test("Floating point literals", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    for (i <- floatValues) {
      check(s, Float32Literal(i), Float32Literal(i))
    }


    for (i <- doubleValues) {
      check(s, Float64Literal(i), Float64Literal(i))
    }

  }

  test("Floating Point Arithmetic", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    for (i <- floatValues; j <- floatValues) {
      check(s, Plus(Float32Literal(i), Float32Literal(j)), Float32Literal(i + j))
      check(s, Minus(Float32Literal(i), Float32Literal(j)), Float32Literal(i - j))
      check(s, Times(Float32Literal(i), Float32Literal(j)), Float32Literal(i * j))
      check(s, Division(Float32Literal(i), Float32Literal(j)), Float32Literal(i / j))
    }

    for (i <- floatValues) {
      check(s, UMinus(Float32Literal(i)), Float32Literal(-i))
    }

    for (i <- doubleValues; j <- doubleValues) {
      check(s, Plus(Float64Literal(i), Float64Literal(j)), Float64Literal(i + j))
      check(s, Minus(Float64Literal(i), Float64Literal(j)), Float64Literal(i - j))
      check(s, Times(Float64Literal(i), Float64Literal(j)), Float64Literal(i * j))
      check(s, Division(Float64Literal(i), Float64Literal(j)), Float64Literal(i / j))
    }

    for (i <- doubleValues) {
      check(s, UMinus(Float64Literal(i)), Float64Literal(-i))
    }

  }

  test("Floating Point Comparisons", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)


    for (i <- floatValues; j <- floatValues) {
      check(s, FPEquals(Float32Literal(i), Float32Literal(j)), BooleanLiteral(Float32Literal(i).semEquals(Float32Literal(j))))
      check(s, FPEquals(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i == j))
      check(s, GreaterEquals(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i >= j))
      check(s, GreaterThan(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i > j))
      check(s, LessEquals(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i <= j))
      check(s, LessThan(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i < j))
    }

    for (i <- floatValues.excl(0)) {
      check(s, FPIsNegative(Float32Literal(i)), BooleanLiteral(i < 0))
    }
    check(s, FPIsNegative(Float32Literal(-0)), BooleanLiteral(true))
    check(s, FPIsNegative(Float32Literal(0)), BooleanLiteral(false))

    for (i <- floatValues.excl(0)) {
      check(s, FPIsPositive(Float32Literal(i)), BooleanLiteral(i > 0))
    }
    check(s, FPIsPositive(Float32Literal(0)), BooleanLiteral(true))
    check(s, FPIsPositive(Float32Literal(-0)), BooleanLiteral(false))

    for (i <- floatValues) {
      check(s, FPIsInfinite(Float32Literal(i)), BooleanLiteral(i == Float.PositiveInfinity || i == Float.NegativeInfinity))
    }

    for (i <- floatValues) {
      check(s, FPIsZero(Float32Literal(i)), BooleanLiteral(i == 0))
    }

    check(s, FPIsNaN(Float32Literal(Float.NaN)), BooleanLiteral(true))

    for (i <- doubleValues; j <- doubleValues) {
      check(s, FPEquals(Float64Literal(i), Float64Literal(j)), BooleanLiteral(Float64Literal(i).semEquals(Float64Literal(j))))
      check(s, FPEquals(Float64Literal(i), Float64Literal(j)), BooleanLiteral(i == j))
      check(s, GreaterEquals(Float64Literal(i), Float64Literal(j)), BooleanLiteral(i >= j))
      check(s, GreaterThan(Float64Literal(i), Float64Literal(j)), BooleanLiteral(i > j))
      check(s, LessEquals(Float64Literal(i), Float64Literal(j)), BooleanLiteral(i <= j))
      check(s, LessThan(Float64Literal(i), Float64Literal(j)), BooleanLiteral(i < j))
    }

    for (i <- doubleValues.excl(0)) {
      check(s, FPIsNegative(Float64Literal(i)), BooleanLiteral(i < 0))
    }
    check(s, FPIsNegative(Float64Literal(-0)), BooleanLiteral(true))
    check(s, FPIsNegative(Float64Literal(0)), BooleanLiteral(false))

    for (i <- doubleValues.excl(0)) {
      check(s, FPIsPositive(Float64Literal(i)), BooleanLiteral(i > 0))
    }
    check(s, FPIsPositive(Float64Literal(0)), BooleanLiteral(true))
    check(s, FPIsPositive(Float64Literal(-0)), BooleanLiteral(false))

    for (i <- doubleValues) {
      check(s, FPIsInfinite(Float64Literal(i)), BooleanLiteral(i == Double.PositiveInfinity || i == Double.NegativeInfinity))
    }

    for (i <- doubleValues) {
      check(s, FPIsZero(Float64Literal(i)), BooleanLiteral(i == 0))
    }

    check(s, FPIsNaN(Float64Literal(Double.NaN)), BooleanLiteral(true))



  }
  test("Let") { ctx =>
    val s = solver(ctx)

    val v = Variable.fresh("id", Int32Type())
    check(s, Let(v.toVal, Int32Literal(42), v), Int32Literal(42))
    check(s, Let(v.toVal, Int32Literal(42), Plus(v, Int32Literal(1))), Int32Literal(43))
  }

  test("Map Operations", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    check(s, Equals(
      FiniteMap(Seq.empty, Int32Literal(12), Int32Type(), Int32Type()),
      FiniteMap(Seq.empty, Int32Literal(12), Int32Type(), Int32Type())
    ), BooleanLiteral(true))

    val v = Variable.fresh("v", Int32Type())

    assert(s.solveVALID(Equals(
      MapApply(FiniteMap(Seq.empty, Int32Literal(9), Int32Type(), Int32Type()), v),
      MapApply(FiniteMap(Seq.empty, Int32Literal(12), Int32Type(), Int32Type()), v)
    )) contains false)

    assert(s.solveVALID(Equals(
      MapApply(FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type()), v),
      MapApply(FiniteMap(Seq(Int32Literal(2) -> Int32Literal(3), Int32Literal(1) -> Int32Literal(2)), Int32Literal(9), Int32Type(), Int32Type()), v)
    )) contains true)

    assert(s.solveVALID(Equals(
      MapApply(FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type()), v),
      MapApply(FiniteMap(Seq(Int32Literal(2) -> Int32Literal(3), Int32Literal(1) -> Int32Literal(2)), Int32Literal(9), Int32Type(), Int32Type()), v)
    )) contains true)

    assert(s.solveVALID(Equals(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(1) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type()),
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(3), Int32Literal(1) -> Int32Literal(2)), Int32Literal(9), Int32Type(), Int32Type())
    )) contains false)

    assert(s.solveVALID(Equals(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(1) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type()),
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type())
    )) contains true)

    check(s, MapApply(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type(), Int32Type()),
      Int32Literal(1)
    ), Int32Literal(2))

    check(s, MapApply(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type(), Int32Type()),
      Int32Literal(3)
    ), Int32Literal(6))

    check(s, MapApply(
      MapUpdated(
        FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type(), Int32Type()),
        Int32Literal(1), Int32Literal(3)),
      Int32Literal(1)
    ), Int32Literal(3))
  }

  test("Set Operations", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    check(s, Equals(
      FiniteSet(Seq.empty, Int32Type()),
      FiniteSet(Seq.empty, Int32Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      FiniteSet(Seq(Int32Literal(9)), Int32Type()),
      FiniteSet(Seq.empty, Int32Type())
    ), BooleanLiteral(false))

    check(s, Equals(
      FiniteSet(Seq(Int8Literal(1), Int8Literal(2)), Int8Type()),
      FiniteSet(Seq(Int8Literal(2), Int8Literal(1)), Int8Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
      FiniteSet(Seq(Int32Literal(2), Int32Literal(1)), Int32Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2), Int32Literal(1)), Int32Type())
    ), BooleanLiteral(true))

    check(s, ElementOfSet(
      Int32Literal(1),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type())
    ), BooleanLiteral(true))

    check(s, ElementOfSet(
      Int32Literal(2),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type())
    ), BooleanLiteral(true))

    check(s, ElementOfSet(
      Int32Literal(3),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type())
    ), BooleanLiteral(false))

    check(s, ElementOfSet(
      Int32Literal(3),
      SetAdd(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()), Int32Literal(3))
    ), BooleanLiteral(true))

    val v = Variable.fresh("v", Int32Type())

    assert(s.solveVALID(let(
      "s" :: SetType(Int32Type()),
      SetUnion(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()), FiniteSet(Seq(Int32Literal(1)), Int32Type()))
    )(s => And(
      ElementOfSet(Int32Literal(1), s),
      ElementOfSet(Int32Literal(2), s)
    ))) contains true)

    assert(s.solveVALID(let(
      "s" :: SetType(Int32Type()),
      SetUnion(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()), FiniteSet(Seq(Int32Literal(1)), Int32Type()))
    )(s => or(Equals(v, Int32Literal(1)), Equals(v, Int32Literal(2)), Not(ElementOfSet(v, s))))) contains true)

    assert(s.solveVALID(or(
      Equals(v, Int32Literal(2)), Not(ElementOfSet(v, SetDifference(
        FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
        FiniteSet(Seq(Int32Literal(1)), Int32Type())
      )))
    )) contains true)

    assert(s.solveVALID(or(
      Equals(v, Int32Literal(2)), Not(ElementOfSet(v, SetDifference(
        FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
        FiniteSet(Seq.empty, Int32Type())
      )))
    )) contains false)

    assert(s.solveVALID(or(
      Equals(v, Int32Literal(2)), Not(ElementOfSet(v, SetIntersection(
        FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
        FiniteSet(Seq(Int32Literal(2)), Int32Type())
      )))
    )) contains true)
  }

  test("Z3 Set Extraction", filterSolvers(_, princess = true, cvc4 = true, cvc5 = true)) { ctx =>
    val s = solver(ctx)

    // Singleton set inside of a map is translated to (lambda ((x Int)) (= x 0))
    check(s,
      FiniteMap(Seq(), FiniteSet(Seq(IntegerLiteral(0)), IntegerType()), IntegerType(), SetType(IntegerType())),
      FiniteMap(Seq(), FiniteSet(Seq(IntegerLiteral(0)), IntegerType()), IntegerType(), SetType(IntegerType()))
    )
  }

  test("Simple Bag Operations", filterSolvers(_, princess = true)) { ctx =>
    val s = solver(ctx)

    assert(s.solveVALID(Equals(
      FiniteBag(Seq.empty, Int32Type()),
      FiniteBag(Seq.empty, Int32Type())
    )) contains true)

    assert(s.solveVALID(Equals(
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(1), Int32Literal(2) -> IntegerLiteral(2)), Int32Type()),
      FiniteBag(Seq(Int32Literal(2) -> IntegerLiteral(2), Int32Literal(1) -> IntegerLiteral(1)), Int32Type())
    )) contains true)

    assert(s.solveVALID(Equals(
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(1)), Int32Type()),
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(2), Int32Literal(1) -> IntegerLiteral(1)), Int32Type())
    )) contains true)

    check(s, MultiplicityInBag(
      Int32Literal(1),
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(2)), Int32Type())
    ), IntegerLiteral(2))
  }

  test("Bag Operations", filterSolvers(_, princess = true, cvc4 = true, cvc5 = true)) { ctx =>
    val s = solver(ctx)

    check(s, Equals(
      FiniteBag(Seq(Int32Literal(9) -> IntegerLiteral(1)), Int32Type()),
      FiniteBag(Seq.empty, Int32Type())
    ), BooleanLiteral(false))

    check(s, MultiplicityInBag(
      Int32Literal(2),
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(2)), Int32Type())
    ), IntegerLiteral(0))

    check(s, MultiplicityInBag(
      Int32Literal(1),
      BagAdd(FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(1)), Int32Type()), Int32Literal(1))
    ), IntegerLiteral(2))

    check(s, Equals(
      BagUnion(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type()),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(1),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type())
      ),
      FiniteBag(Seq(
        Int32Literal(1) -> IntegerLiteral(1),
        Int32Literal(2) -> IntegerLiteral(3),
        Int32Literal(3) -> IntegerLiteral(1)
      ), Int32Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      BagUnion(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type()),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(2),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type())
      ),
      FiniteBag(Seq(
        Int32Literal(1) -> IntegerLiteral(1),
        Int32Literal(2) -> IntegerLiteral(3),
        Int32Literal(3) -> IntegerLiteral(1)
      ), Int32Type())
    ), BooleanLiteral(false))

    check(s, Equals(
      BagDifference(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type()),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(3),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type())
      ),
      FiniteBag(Seq(
        Int32Literal(1) -> IntegerLiteral(1)
      ), Int32Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      BagIntersection(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type()),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(3),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type())
      ),
      FiniteBag(Seq(
        Int32Literal(2) -> IntegerLiteral(2)
      ), Int32Type())
    ), BooleanLiteral(true))
  }
}
