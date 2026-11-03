/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Bit-vector arithmetic, casts and bitwise operations on every solver. */
class BitVectorSemanticsSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  given Symbols = symbols

  test("BitVector Literals") { ctx =>
    val s = solver(ctx)

    val twoTo64 = BigInt(2).pow(64)
    val twoTo100 = BigInt(2).pow(100)

    check(s, BVLiteral(true, 0, 13),                  BVLiteral(true, 0, 13))
    check(s, BVLiteral(true, -1, 13),                 BVLiteral(true, -1, 13))
    check(s, BVLiteral(true, -twoTo64, 65),           BVLiteral(true, -twoTo64, 65))
    check(s, BVLiteral(true, twoTo100 - 1, 101),      BVLiteral(true, twoTo100 - 1, 101))
    check(s, BVLiteral(false, twoTo64 - 1, 64),       BVLiteral(false, twoTo64 - 1, 64))
    check(s, BVLiteral(false, twoTo100 + 123, 128),   BVLiteral(false, twoTo100 + 123, 128))
    check(s, Int64Literal(-1),                        Int64Literal(-1))
    check(s, Int64Literal(4294967296L),               Int64Literal(4294967296L))
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

  test("BitVector Arithmetic Bis", BitVectors) { ctx =>
    val s = solver(ctx)

    check(s, Plus(BVLiteral(true, 3, 13), BVLiteral(true, 5, 13)),              BVLiteral(true, 8, 13))
    check(s, Plus(BVLiteral(true, 3, 16), BVLiteral(true, 5, 16)),              BVLiteral(true, 8, 16))
    check(s, Plus(BVLiteral(false, 3, 13), BVLiteral(false, 5, 13)),            BVLiteral(false, 8, 13))
    check(s, Plus(BVLiteral(false, 3, 16), BVLiteral(false, 5, 16)),            BVLiteral(false, 8, 16))
    check(s, Plus(BVLiteral(true, Short.MaxValue, 16), BVLiteral(true, 1, 16)), BVLiteral(true, Short.MinValue, 16))
    check(s, Plus(BVLiteral(false, Short.MaxValue, 16), BVLiteral(false, 1, 16)), BVLiteral(false, BigInt(Short.MaxValue) + 1, 16))
  }

  test("BitVector Casts", BitVectors) { ctx =>
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

  test("BitVector/Integer Conversions", Integers, BitVectorIntConversions) { ctx =>
    val s = solver(ctx)

    check(s, BVToInt(BVLiteral(false, 42, 8)), IntegerLiteral(42))
    check(s, BVToInt(BVLiteral(false, 255, 8)), IntegerLiteral(255))
    check(s, BVToInt(Int8Literal(-1)),          IntegerLiteral(-1))
    check(s, BVToInt(Int8Literal(Byte.MinValue)), IntegerLiteral(Byte.MinValue))
    check(s, BVToInt(BVUnsignedToSigned(BVLiteral(false, 255, 8))), IntegerLiteral(-1))
    check(s, BVToInt(BVSignedToUnsigned(Int8Literal(-1))), IntegerLiteral(255))

    check(s, IntToBV(8, true, IntegerLiteral(42)),   Int8Literal(42))
    check(s, IntToBV(8, true, IntegerLiteral(-1)),   Int8Literal(-1))
    check(s, IntToBV(8, true, IntegerLiteral(255)),  Int8Literal(-1))
    check(s, IntToBV(8, true, IntegerLiteral(-214)), Int8Literal(42))
    check(s, IntToBV(8, false, IntegerLiteral(-1)),  BVLiteral(false, 255, 8))
    check(s, IntToBV(8, false, IntegerLiteral(810)), BVLiteral(false, 42, 8))

    val signed = Variable.fresh("signed", Int8Type())
    val unsigned = Variable.fresh("unsigned", BVType(false, 8))

    assert(s.solveVALID(Equals(IntToBV(8, true, BVToInt(signed)), signed)).contains(true))
    assert(s.solveVALID(Equals(IntToBV(8, false, BVToInt(unsigned)), unsigned)).contains(true))
  }

  test("solve bitwise operations", BitVectors) { ctx =>
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

  test("BitVector Comparisons", BitVectors) { ctx =>
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

  test("BitVector Division, Remainder and Modulo", BitVectors) { ctx =>
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

  test("BitVector Modulo by the minimal value") { ctx =>
    val s = solver(ctx)

    // `x mod |y|` cannot be computed as `x mod -y` when `y` is the minimal value
    check(s, Modulo(Int8Literal(1), Int8Literal(-128)),   Int8Literal(1))
    check(s, Modulo(Int8Literal(-1), Int8Literal(-128)),  Int8Literal(127))
    check(s, Modulo(Int8Literal(-128), Int8Literal(-128)), Int8Literal(0))
    check(s, Modulo(Int8Literal(-3), Int8Literal(-2)),    Int8Literal(1))
    check(s, Modulo(Int32Literal(5), Int32Literal(Int.MinValue)), Int32Literal(5))
    check(s, Modulo(Int32Literal(-5), Int32Literal(Int.MinValue)), Int32Literal(Int.MaxValue - 4))

    val x = Variable.fresh("x", Int8Type())
    val y = Variable.fresh("y", Int8Type())
    assert(s.solveVALID(Implies(
      Not(Equals(y, Int8Literal(0))),
      And(GreaterEquals(Modulo(x, y), Int8Literal(0)), Not(Equals(Modulo(x, y), y)))
    )) contains true)
  }

  object UInt32Type extends BVTypeExtractor(false, 32)

  test("Signed and unsigned overflows") { ctx =>
    val s = solver(ctx)
    val zero = Int32Literal(0)
    val uzero = BVLiteral(false, 0, 32)
    val x = Variable.fresh("x", Int32Type())
    val y = Variable.fresh("y", Int32Type())
    val ux = Variable.fresh("ux", UInt32Type())
    val uy = Variable.fresh("uy", UInt32Type())

    assert(s.solveSAT(x > zero && y > zero && x + y < zero).isSAT)
    assert(s.solveSAT(x < zero && y < zero && x - y > zero).isSAT)
    assert(s.solveSAT(ux + uy < ux).isSAT)
    assert(s.solveSAT(ux - uy > ux).isSAT)
  }

  for ((tpe, sign) <- Seq(Int32Type() -> "Signed", UInt32Type() -> "Unsigned")) {
    test(s"$sign bit-vector algebraic laws") { ctx =>
      val s = solver(ctx)
      val x = Variable.fresh("x", tpe)
      val y = Variable.fresh("y", tpe)
      val z = Variable.fresh("z", tpe)

      assert(s.solveSAT(x + (y + z) !== (x + y) + z).isUNSAT, "associativity")
      assert(s.solveSAT(x + y !== y + x).isUNSAT, "commutativity")
      assert(s.solveSAT(x * (y + z) !== x * y + x * z).isUNSAT, "distributivity")
    }
  }
}
