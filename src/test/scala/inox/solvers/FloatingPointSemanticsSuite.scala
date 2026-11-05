/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** IEEE floating point operations on every solver. */
class FloatingPointSemanticsSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  given Symbols = symbols

  import scala.collection.immutable.HashSet
  val floatValues: Set[Float] = HashSet(0f, 1.4, -0f, Float.NaN, Float.PositiveInfinity, Float.NegativeInfinity)

  // SMT-LIB's fp.max and fp.min ignore a NaN operand unless both are NaN, and Inox orders
  // -0.0 below +0.0, which SMT-LIB leaves open.
  def smtMax(a: Float, b: Float): Float = if (a.isNaN) b else if (b.isNaN) a else a.max(b)
  def smtMin(a: Float, b: Float): Float = if (a.isNaN) b else if (b.isNaN) a else a.min(b)

  test("Floating point literals", FloatingPoint) { ctx =>
    val s = solver(ctx)

    for (i <- floatValues) {
      check(s, Float32Literal(i), Float32Literal(i))
    }

  }

  test("Floating Point Arithmetic", FloatingPoint) { ctx =>
    val s = solver(ctx)

    for (i <- floatValues; j <- floatValues) {
      check(s, FPAdd(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j)), Float32Literal(i + j))
      check(s, FPSub(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j)), Float32Literal(i - j))
      check(s, FPMul(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j)), Float32Literal(i * j))
      check(s, FPDiv(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j)), Float32Literal(i / j))
      check(s, FPFMA(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j), Float32Literal(j)), Float32Literal(java.lang.Math.fma(i, j, j)))
      check(s, FPMax(Float32Literal(i), Float32Literal(j)), Float32Literal(smtMax(i, j)))
      check(s, FPMin(Float32Literal(i), Float32Literal(j)), Float32Literal(smtMin(i, j)))
    }

    for (i <- floatValues) {
      check(s, FPUMinus(Float32Literal(i)), Float32Literal(-i))
      check(s, FPAbs(Float32Literal(i)), Float32Literal(Math.abs(i)))
      check(s, ToDouble(Float32Literal(i)), Float64Literal(i.toDouble))
      check(s, FPToBVJVM(8, 24, 8, Float32Literal(i)), Int8Literal(i.toByte))
      check(s, FPToBVJVM(8, 24, 16, Float32Literal(i)), Int16Literal(i.toShort))
      check(s, FPToBVJVM(8, 24, 32, Float32Literal(i)), Int32Literal(i.toInt))
      check(s, FPToBVJVM(8, 24, 64, Float32Literal(i)), Int64Literal(i.toLong))
      check(s, FPFromBinary(8, 24, FPToBinary(8, 24, Float32Literal(i))), Float32Literal(i))
      check(s, Sqrt(RoundNearestTiesToEven, Float64Literal(i)), Float64Literal(math.sqrt(i)))
      check(s, FPRound(RoundNearestTiesToEven, Float64Literal(i.toDouble)), Float64Literal(Math.rint(i.toDouble)))
      check(s, FPRound(RoundTowardNegative, Float64Literal(i.toDouble)), Float64Literal(Math.floor(i.toDouble)))
      check(s, FPRound(RoundTowardPositive, Float64Literal(i.toDouble)), Float64Literal(Math.ceil(i.toDouble)))
      check(s, ToDouble(Float32Literal(i)), Float64Literal(i))
      check(s, ToFloat(FPMul(RoundNearestTiesToEven, Float64Literal(i), Float64Literal(i))), Float32Literal((i.toDouble * i.toDouble).toFloat))
    }

  }

  test("Floating Point Comparisons", FloatingPoint) { ctx =>
    val s = solver(ctx)

    for (i <- floatValues; j <- floatValues) {
      check(s, FPEquals(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i == j))
      check(s, FPGreaterEquals(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i >= j))
      check(s, FPGreaterThan(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i > j))
      check(s, FPLessEquals(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i <= j))
      check(s, FPLessThan(Float32Literal(i), Float32Literal(j)), BooleanLiteral(i < j))
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

  }
}
