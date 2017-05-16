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
    eval(e, Int8Literal(-1))        === Int8Literal(-1)
    eval(e, Int8Literal(-128))      === Int8Literal(-128)
    eval(e, Int8Literal(0))         === Int8Literal(0)
    eval(e, Int8Literal(58))        === Int8Literal(58)
    eval(e, Int16Literal(58))       === Int16Literal(58)
    eval(e, Int16Literal(-1))       === Int16Literal(-1)
    eval(e, Int16Literal(0))        === Int16Literal(0)
    eval(e, Int32Literal(-1))       === Int32Literal(-1)
    eval(e, Int32Literal(0))        === Int32Literal(0)
    eval(e, Int32Literal(42))       === Int32Literal(42)
    eval(e, Int64Literal(58))       === Int64Literal(58)
    eval(e, Int64Literal(-1))       === Int64Literal(-1)
    eval(e, Int64Literal(4294967296L)) === Int64Literal(4294967296L)
    eval(e, BVLiteral(0, 13))       === BVLiteral(0, 13)
    eval(e, BVLiteral(261, 13))     === BVLiteral(261, 13)
    eval(e, BVLiteral(-1, 33))      === BVLiteral(-1, 33)
    eval(e, BVLiteral(4294967296L, 33)) === BVLiteral(4294967296L, 33) // 2^32 fits in 33 bits!
    eval(e, UnitLiteral())          === UnitLiteral()
    eval(e, IntegerLiteral(0))      === IntegerLiteral(0)
    eval(e, IntegerLiteral(42))     === IntegerLiteral(42)
    eval(e, IntegerLiteral(1099511627776L)) === IntegerLiteral(1099511627776L) // 2^40
    eval(e, FractionLiteral(0, 1))  === FractionLiteral(0, 1)
    eval(e, FractionLiteral(42 ,1)) === FractionLiteral(42, 1)
    eval(e, FractionLiteral(26, 3)) === FractionLiteral(26, 3)
  }

  test("BitVector Arithmetic") {
    val e = evaluator(ctx)

    eval(e, Plus(Int8Literal(3), Int8Literal(5)))             === Int8Literal(8)
    eval(e, Plus(Int8Literal(-127), Int8Literal(-1)))         === Int8Literal(-128)
    eval(e, Plus(Int8Literal(Byte.MaxValue), Int8Literal(1))) === Int8Literal(Byte.MinValue)
    eval(e, Times(Int8Literal(3), Int8Literal(3)))            === Int8Literal(9)

    eval(e, Plus(Int32Literal(3), Int32Literal(5)))             === Int32Literal(8)
    eval(e, Plus(Int32Literal(0), Int32Literal(5)))             === Int32Literal(5)
    eval(e, Plus(Int32Literal(1), Int32Literal(-2)))            === Int32Literal(-1)
    eval(e, Plus(Int32Literal(Int.MaxValue), Int32Literal(1)))  === Int32Literal(Int.MinValue)
    eval(e, Times(Int32Literal(3), Int32Literal(3)))            === Int32Literal(9)

    eval(e, Plus(BVLiteral(3, 13), BVLiteral(5, 13)))               === BVLiteral(8, 13)
    eval(e, Plus(BVLiteral(3, 16), BVLiteral(5, 16)))               === BVLiteral(8, 16)
    eval(e, Plus(BVLiteral(Short.MaxValue, 16), BVLiteral(1, 16)))  === BVLiteral(Short.MinValue, 16)

    eval(e, BVWideningCast(Int8Literal(0), Int32Type))    === Int32Literal(0)
    eval(e, BVWideningCast(Int8Literal(1), Int32Type))    === Int32Literal(1)
    eval(e, BVWideningCast(BVLiteral(2, 3), BVType(4)))   === BVLiteral(2, 4)
    eval(e, BVWideningCast(Int8Literal(1), BVType(9)))    === BVLiteral(1, 9)
    eval(e, BVWideningCast(BVLiteral(1, 2), Int32Type))   === Int32Literal(1)
    eval(e, BVWideningCast(BVLiteral(1, 1), Int32Type))   === Int32Literal(-1) // 2's complement on 1 bit
    eval(e, BVWideningCast(Int8Literal(-1), Int32Type))   === Int32Literal(-1)
    eval(e, BVWideningCast(Int8Literal(-128), Int32Type)) === Int32Literal(-128)

    eval(e, Plus(Int32Literal(1), BVWideningCast(Int8Literal(1), Int32Type))) === Int32Literal(2)

    val b: Byte = 1
    eval(e, Plus(
              BVWideningCast(Int32Literal(Int.MaxValue), Int64Type),
              BVWideningCast(Int8Literal(1), Int64Type)
            )) === Int64Literal(Int.MaxValue + b.toLong)
    eval(e, Plus(
              BVWideningCast(Int32Literal(Int.MaxValue), Int64Type),
              BVWideningCast(Int8Literal(1), Int64Type)
            )) !== Int64Literal(Int.MaxValue + b.toInt) // mind the `toInt` instead of `toLong`

    eval(e, BVNarrowingCast(Int8Literal(1), BVType(7)))     === BVLiteral(1, 7)
    eval(e, BVNarrowingCast(Int32Literal(1), Int8Type))     === Int8Literal(1)
    eval(e, BVNarrowingCast(BVLiteral(1, 33), Int32Type))   === Int32Literal(1)
    eval(e, BVNarrowingCast(Int32Literal(-1), Int8Type))    === Int8Literal(-1)
    eval(e, BVNarrowingCast(Int32Literal(-128), Int8Type))  === Int8Literal(-128)
    eval(e, BVNarrowingCast(Int32Literal(-129), Int8Type))  === Int8Literal(127)
    eval(e, BVNarrowingCast(Int32Literal(128), Int8Type))   === Int8Literal(-128)
  }

  test("eval bitwise operations") {
    val e = evaluator(ctx)

    eval(e, BVAnd(Int8Literal(3), Int8Literal(1)))          === Int8Literal(1)
    eval(e, BVOr(Int8Literal(5), Int8Literal(3)))           === Int8Literal(7)
    eval(e, BVXor(Int8Literal(3), Int8Literal(1)))          === Int8Literal(2)
    eval(e, BVNot(Int8Literal(1)))                          === Int8Literal(-2)
    eval(e, BVShiftLeft(Int8Literal(3), Int8Literal(1)))    === Int8Literal(6)
    eval(e, BVAShiftRight(Int8Literal(8), Int8Literal(1)))  === Int8Literal(4)

    eval(e, BVAnd(Int32Literal(3), Int32Literal(1))) === Int32Literal(1)
    eval(e, BVAnd(Int32Literal(3), Int32Literal(3))) === Int32Literal(3)
    eval(e, BVAnd(Int32Literal(5), Int32Literal(3))) === Int32Literal(1)
    eval(e, BVAnd(Int32Literal(5), Int32Literal(4))) === Int32Literal(4)
    eval(e, BVAnd(Int32Literal(5), Int32Literal(2))) === Int32Literal(0)

    eval(e, BVOr(Int32Literal(3), Int32Literal(1))) === Int32Literal(3)
    eval(e, BVOr(Int32Literal(3), Int32Literal(3))) === Int32Literal(3)
    eval(e, BVOr(Int32Literal(5), Int32Literal(3))) === Int32Literal(7)
    eval(e, BVOr(Int32Literal(5), Int32Literal(4))) === Int32Literal(5)
    eval(e, BVOr(Int32Literal(5), Int32Literal(2))) === Int32Literal(7)

    eval(e, BVXor(Int32Literal(3), Int32Literal(1))) === Int32Literal(2)
    eval(e, BVXor(Int32Literal(3), Int32Literal(3))) === Int32Literal(0)

    eval(e, BVNot(Int32Literal(1))) === Int32Literal(-2)

    eval(e, BVShiftLeft(Int32Literal(3), Int32Literal(1))) === Int32Literal(6)
    eval(e, BVShiftLeft(Int32Literal(4), Int32Literal(2))) === Int32Literal(16)

    eval(e, BVLShiftRight(Int32Literal(8), Int32Literal(1))) === Int32Literal(4)
    eval(e, BVAShiftRight(Int32Literal(8), Int32Literal(1))) === Int32Literal(4)

    eval(e, BVNarrowingCast(
              BVAnd(BVWideningCast(Int8Literal(1), Int32Type),
                    BVWideningCast(Int8Literal(2), Int32Type)),
              Int8Type)
    ) === Int8Literal(0)

    def bvl(x: BigInt) = BVLiteral(x, 11)
    eval(e, BVAnd(bvl(3), bvl(1)))          === bvl(1)
    eval(e, BVOr(bvl(5), bvl(3)))           === bvl(7)
    eval(e, BVXor(bvl(3), bvl(1)))          === bvl(2)
    eval(e, BVNot(bvl(1)))                  === bvl(-2)
    eval(e, BVShiftLeft(bvl(3), bvl(1)))    === bvl(6)
    eval(e, BVAShiftRight(bvl(8), bvl(1)))  === bvl(4)
  }

  test("BigInt Arithmetic") {
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

  test("BigInt Comparisons") {
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

  test("BitVector Comparisons") {
    val e = evaluator(ctx)

    eval(e, GreaterEquals(Int8Literal(7), Int8Literal(4)))  === BooleanLiteral(true)
    eval(e, GreaterThan(Int8Literal(7), Int8Literal(7)))    === BooleanLiteral(false)
    eval(e, LessEquals(Int8Literal(7), Int8Literal(7)))     === BooleanLiteral(true)
    eval(e, LessThan(Int8Literal(4), Int8Literal(7)))       === BooleanLiteral(true)

    eval(e, GreaterEquals(Int16Literal(7), Int16Literal(4)))  === BooleanLiteral(true)
    eval(e, GreaterThan(Int16Literal(7), Int16Literal(7)))    === BooleanLiteral(false)
    eval(e, LessEquals(Int16Literal(7), Int16Literal(7)))     === BooleanLiteral(true)
    eval(e, LessThan(Int16Literal(4), Int16Literal(7)))       === BooleanLiteral(true)

    eval(e, GreaterEquals(Int64Literal(7), Int64Literal(4)))  === BooleanLiteral(true)
    eval(e, GreaterThan(Int64Literal(7), Int64Literal(7)))    === BooleanLiteral(false)
    eval(e, LessEquals(Int64Literal(7), Int64Literal(7)))     === BooleanLiteral(true)
    eval(e, LessThan(Int64Literal(4), Int64Literal(7)))       === BooleanLiteral(true)

    eval(e, GreaterEquals(Int32Literal(7), Int32Literal(4)))  === BooleanLiteral(true)
    eval(e, GreaterEquals(Int32Literal(7), Int32Literal(7)))  === BooleanLiteral(true)
    eval(e, GreaterEquals(Int32Literal(4), Int32Literal(7)))  === BooleanLiteral(false)

    eval(e, GreaterThan(Int32Literal(7), Int32Literal(4)))    === BooleanLiteral(true)
    eval(e, GreaterThan(Int32Literal(7), Int32Literal(7)))    === BooleanLiteral(false)
    eval(e, GreaterThan(Int32Literal(4), Int32Literal(7)))    === BooleanLiteral(false)

    eval(e, LessEquals(Int32Literal(7), Int32Literal(4)))     === BooleanLiteral(false)
    eval(e, LessEquals(Int32Literal(7), Int32Literal(7)))     === BooleanLiteral(true)
    eval(e, LessEquals(Int32Literal(4), Int32Literal(7)))     === BooleanLiteral(true)

    eval(e, LessThan(Int32Literal(7), Int32Literal(4)))       === BooleanLiteral(false)
    eval(e, LessThan(Int32Literal(7), Int32Literal(7)))       === BooleanLiteral(false)
    eval(e, LessThan(Int32Literal(4), Int32Literal(7)))       === BooleanLiteral(true)

    def bvl(x: BigInt) = BVLiteral(x, 13)
    eval(e, GreaterEquals(bvl(7), bvl(4)))  === BooleanLiteral(true)
    eval(e, GreaterThan(bvl(7), bvl(7)))    === BooleanLiteral(false)
    eval(e, LessEquals(bvl(7), bvl(7)))     === BooleanLiteral(true)
    eval(e, LessThan(bvl(4), bvl(7)))       === BooleanLiteral(true)
  }

  test("BitVector Division, Remainder and Modulo") {
    val e = evaluator(ctx)

    eval(e, Division(Int32Literal(10), Int32Literal(3)))    === Int32Literal(3)
    eval(e, Remainder(Int32Literal(10), Int32Literal(3)))   === Int32Literal(1)
    eval(e, Modulo(Int32Literal(10), Int32Literal(3)))      === Int32Literal(1)

    eval(e, Division(Int32Literal(-1), Int32Literal(3)))    === Int32Literal(0)
    eval(e, Remainder(Int32Literal(-1), Int32Literal(3)))   === Int32Literal(-1)
    eval(e, Modulo(Int32Literal(-1), Int32Literal(3)))      === Int32Literal(2)

    eval(e, Division(Int32Literal(-1), Int32Literal(-3)))   === Int32Literal(0)
    eval(e, Remainder(Int32Literal(-1), Int32Literal(-3)))  === Int32Literal(-1)
    eval(e, Modulo(Int32Literal(-1), Int32Literal(-3)))     === Int32Literal(2)

    eval(e, Division(Int32Literal(1), Int32Literal(-3)))    === Int32Literal(0)
    eval(e, Remainder(Int32Literal(1), Int32Literal(-3)))   === Int32Literal(1)
    eval(e, Modulo(Int32Literal(1), Int32Literal(-3)))      === Int32Literal(1)

    eval(e, Division(Int8Literal(1), Int8Literal(-3)))      === Int8Literal(0)
    eval(e, Remainder(Int8Literal(1), Int8Literal(-3)))     === Int8Literal(1)
    eval(e, Remainder(Int8Literal(-1), Int8Literal(3)))     === Int8Literal(-1)
    eval(e, Modulo(Int8Literal(-1), Int8Literal(3)))        === Int8Literal(2)
    eval(e, Division(Int16Literal(1), Int16Literal(-3)))    === Int16Literal(0)
    eval(e, Remainder(Int16Literal(1), Int16Literal(-3)))   === Int16Literal(1)
    eval(e, Remainder(Int16Literal(-1), Int16Literal(3)))   === Int16Literal(-1)
    eval(e, Modulo(Int16Literal(-1), Int16Literal(3)))      === Int16Literal(2)
    eval(e, Division(Int64Literal(1), Int64Literal(-3)))    === Int64Literal(0)
    eval(e, Remainder(Int64Literal(1), Int64Literal(-3)))   === Int64Literal(1)
    eval(e, Remainder(Int64Literal(-1), Int64Literal(3)))   === Int64Literal(-1)
    eval(e, Modulo(Int64Literal(-1), Int64Literal(3)))      === Int64Literal(2)

    def bvl(x: BigInt) = BVLiteral(x, 13)
    eval(e, Division(bvl(1), bvl(-3)))    === bvl(0)
    eval(e, Remainder(bvl(1), bvl(-3)))   === bvl(1)
    eval(e, Remainder(bvl(-1), bvl(3)))   === bvl(-1)
    eval(e, Modulo(bvl(-1), bvl(3)))      === bvl(2)
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

    eval(e, v, Map(v.toVal -> Int32Literal(23))) === Int32Literal(23)
  }

  test("Undefined Variable") {
    val e = evaluator(ctx)

    val v1 = Variable.fresh("id", Int32Type)
    val v2 = Variable.fresh("foo", Int32Type)

    eval(e, v1, Map(v2.toVal -> Int32Literal(23))).failed
  }

  test("Let") {
    val e = evaluator(ctx)

    val v = Variable.fresh("id", Int32Type)
    eval(e, Let(v.toVal, Int32Literal(42), v)) === Int32Literal(42)
    eval(e, Let(v.toVal, Int32Literal(42), Plus(v, Int32Literal(1)))) === Int32Literal(43)
  }

  test("Map Operations") {
    val e = evaluator(ctx)

    eval(e, Equals(
      FiniteMap(Seq.empty, Int32Literal(12), Int32Type, Int32Type),
      FiniteMap(Seq.empty, Int32Literal(12), Int32Type, Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteMap(Seq.empty, Int32Literal(9), Int32Type, Int32Type),
      FiniteMap(Seq.empty, Int32Literal(12), Int32Type, Int32Type))
    ) === BooleanLiteral(false)

    eval(e, Equals(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(3)), Int32Literal(9), Int32Type, Int32Type),
      FiniteMap(Seq(Int32Literal(2) -> Int32Literal(3), Int32Literal(1) -> Int32Literal(2)), Int32Literal(9), Int32Type, Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(1) -> Int32Literal(3)), Int32Literal(9), Int32Type, Int32Type),
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(3), Int32Literal(1) -> Int32Literal(2)), Int32Literal(9), Int32Type, Int32Type))
    ) === BooleanLiteral(false)

    eval(e, Equals(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(1) -> Int32Literal(3)), Int32Literal(9), Int32Type, Int32Type),
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(3)), Int32Literal(9), Int32Type, Int32Type))
    ) === BooleanLiteral(true)

    eval(e, MapApply(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type, Int32Type),
      Int32Literal(1))
    ) === Int32Literal(2)

    eval(e, MapApply(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type, Int32Type),
      Int32Literal(3))
    ) === Int32Literal(6)

    eval(e, MapApply(
      MapUpdated(
        FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type, Int32Type),
        Int32Literal(1), Int32Literal(3)),
      Int32Literal(1))
    ) === Int32Literal(3)
  }

  test("Set Operations") {
    val e = evaluator(ctx)

    eval(e, Equals(
      FiniteSet(Seq.empty, Int32Type),
      FiniteSet(Seq.empty, Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteSet(Seq(Int32Literal(9)), Int32Type),
      FiniteSet(Seq.empty, Int32Type))
    ) === BooleanLiteral(false)

    eval(e, Equals(
      FiniteSet(Seq(Int8Literal(1), Int8Literal(2)), Int8Type),
      FiniteSet(Seq(Int8Literal(2), Int8Literal(1)), Int8Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type),
      FiniteSet(Seq(Int32Literal(2), Int32Literal(1)), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteSet(Seq(BVLiteral(1, 3), BVLiteral(2, 3)), BVType(3)),
      FiniteSet(Seq(BVLiteral(2, 3), BVLiteral(1, 3)), BVType(3)))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2), Int32Literal(1)), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, ElementOfSet(
      Int32Literal(1),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, ElementOfSet(
      Int32Literal(2),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, ElementOfSet(
      Int32Literal(3),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type))
    ) === BooleanLiteral(false)

    eval(e, ElementOfSet(
      Int32Literal(3),
      SetAdd(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type), Int32Literal(3)))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      SetUnion(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type), FiniteSet(Seq(Int32Literal(1)), Int32Type)),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      SetUnion(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type), FiniteSet(Seq(Int32Literal(3)), Int32Type)),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2), Int32Literal(3)), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      SetDifference(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type), FiniteSet(Seq(Int32Literal(1)), Int32Type)),
      FiniteSet(Seq(Int32Literal(2)), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      SetDifference(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type), FiniteSet(Seq.empty, Int32Type)),
      FiniteSet(Seq(Int32Literal(2)), Int32Type))
    ) === BooleanLiteral(false)

    eval(e, Equals(
      SetIntersection(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type), FiniteSet(Seq(Int32Literal(2)), Int32Type)),
      FiniteSet(Seq(Int32Literal(2)), Int32Type))
    ) === BooleanLiteral(true)
  }

  test("Bag Operations") {
    val e = evaluator(ctx)

    eval(e, Equals(
      FiniteBag(Seq.empty, Int32Type),
      FiniteBag(Seq.empty, Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteBag(Seq(Int32Literal(9) -> IntegerLiteral(1)), Int32Type),
      FiniteBag(Seq.empty, Int32Type))
    ) === BooleanLiteral(false)

    eval(e, Equals(
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(1), Int32Literal(2) -> IntegerLiteral(2)), Int32Type),
      FiniteBag(Seq(Int32Literal(2) -> IntegerLiteral(2), Int32Literal(1) -> IntegerLiteral(1)), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(1)), Int32Type),
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(2), Int32Literal(1) -> IntegerLiteral(1)), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, MultiplicityInBag(
      Int32Literal(1),
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(2)), Int32Type))
    ) === IntegerLiteral(2)

    eval(e, MultiplicityInBag(
      Int32Literal(2),
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(2)), Int32Type))
    ) === IntegerLiteral(0)

    eval(e, MultiplicityInBag(
      Int32Literal(1),
      BagAdd(FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(1)), Int32Type), Int32Literal(1)))
    ) === IntegerLiteral(2)

    eval(e, Equals(
      BagUnion(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(1),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type)
      ),
      FiniteBag(Seq(
        Int32Literal(1) -> IntegerLiteral(1),
        Int32Literal(2) -> IntegerLiteral(3),
        Int32Literal(3) -> IntegerLiteral(1)
      ), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      BagUnion(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(2),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type)
      ),
      FiniteBag(Seq(
        Int32Literal(1) -> IntegerLiteral(1),
        Int32Literal(2) -> IntegerLiteral(3),
        Int32Literal(3) -> IntegerLiteral(1)
      ), Int32Type))
    ) === BooleanLiteral(false)

    eval(e, Equals(
      BagDifference(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(3),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type)
      ),
      FiniteBag(Seq(
        Int32Literal(1) -> IntegerLiteral(1)
      ), Int32Type))
    ) === BooleanLiteral(true)

    eval(e, Equals(
      BagIntersection(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(3),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type)
      ),
      FiniteBag(Seq(
        Int32Literal(2) -> IntegerLiteral(2)
      ), Int32Type))
    ) === BooleanLiteral(true)
  }

  test("Map with variables") {
    val e = evaluator(ctx)

    val v1 = Variable.fresh("v1", Int32Type)
    val v2 = Variable.fresh("v2", Int32Type)
    val v3 = Variable.fresh("v3", Int32Type)

    eval(e, Equals(
      FiniteMap(Seq(v1 -> Int32Literal(2), v2 -> Int32Literal(4)), v3, Int32Type, Int32Type),
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type, Int32Type)),
      Map(v1.toVal -> Int32Literal(1), v2.toVal -> Int32Literal(2), v3.toVal -> Int32Literal(6))
    ) === BooleanLiteral(true)

    eval(e, MapApply(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type, Int32Type),
      v1),
      Map(v1.toVal -> Int32Literal(3))
    ) === Int32Literal(6)

    eval(e, MapApply(
      MapUpdated(
        FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type, Int32Type),
        v1, v2), v3),
      Map(v1.toVal -> Int32Literal(1), v2.toVal -> Int32Literal(3), v3.toVal -> Int32Literal(1))
    ) === Int32Literal(3)
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
