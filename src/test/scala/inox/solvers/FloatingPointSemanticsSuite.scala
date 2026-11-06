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

  // Not a set: -0f == 0f, so a set keeps only one of the two zeros.
  val floatValues: Seq[Float] = Seq(0f, 1.4f, -0f, Float.NaN, Float.PositiveInfinity, Float.NegativeInfinity)

  // SMT-LIB's fp.max and fp.min ignore a NaN operand unless both are NaN, and Inox orders
  // -0.0 below +0.0, which SMT-LIB leaves open.
  def smtMax(a: Float, b: Float): Float = if (a.isNaN) b else if (b.isNaN) a else a.max(b)
  def smtMin(a: Float, b: Float): Float = if (a.isNaN) b else if (b.isNaN) a else a.min(b)
  def smtMax(a: Double, b: Double): Double = if (a.isNaN) b else if (b.isNaN) a else a.max(b)
  def smtMin(a: Double, b: Double): Double = if (a.isNaN) b else if (b.isNaN) a else a.min(b)

  test("Floating point literals", FloatingPoint) { ctx =>
    val s = solver(ctx)

    for (i <- floatValues) {
      check(s, Float32Literal(i), Float32Literal(i))
    }

  }

  // One test per left operand, so that they run in parallel
  for (i <- floatValues) test(s"Floating Point Arithmetic with left operand $i", FloatingPoint) { ctx =>
    val s = solver(ctx)

    for (j <- floatValues) {
      check(s, FPAdd(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j)), Float32Literal(i + j))
      check(s, FPSub(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j)), Float32Literal(i - j))
      check(s, FPMul(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j)), Float32Literal(i * j))
      check(s, FPDiv(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j)), Float32Literal(i / j))
      check(s, FPFMA(RoundNearestTiesToEven, Float32Literal(i), Float32Literal(j), Float32Literal(j)), Float32Literal(java.lang.Math.fma(i, j, j)))
      check(s, FPMax(Float32Literal(i), Float32Literal(j)), Float32Literal(smtMax(i, j)))
      check(s, FPMin(Float32Literal(i), Float32Literal(j)), Float32Literal(smtMin(i, j)))
    }
  }

  test("Floating Point Unary Operations", FloatingPoint) { ctx =>
    val s = solver(ctx)

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

  // Fewer values and operations than for floats, to keep the suite fast: the encodings only
  // differ from those of floats by their sizes.
  val doubleValues: Seq[Double] = Seq(-0d, 2.5, Double.NaN, Double.PositiveInfinity)

  test("Double Precision Operations", FloatingPoint) { ctx =>
    val s = solver(ctx)

    for (i <- doubleValues; j <- doubleValues) {
      check(s, FPAdd(RoundNearestTiesToEven, Float64Literal(i), Float64Literal(j)), Float64Literal(i + j))
      check(s, FPSub(RoundNearestTiesToEven, Float64Literal(i), Float64Literal(j)), Float64Literal(i - j))
      check(s, FPMul(RoundNearestTiesToEven, Float64Literal(i), Float64Literal(j)), Float64Literal(i * j))
      check(s, FPDiv(RoundNearestTiesToEven, Float64Literal(i), Float64Literal(j)), Float64Literal(i / j))
      check(s, FPMax(Float64Literal(i), Float64Literal(j)), Float64Literal(smtMax(i, j)))
      check(s, FPMin(Float64Literal(i), Float64Literal(j)), Float64Literal(smtMin(i, j)))
      check(s, FPEquals(Float64Literal(i), Float64Literal(j)), BooleanLiteral(i == j))
      check(s, FPLessThan(Float64Literal(i), Float64Literal(j)), BooleanLiteral(i < j))
      check(s, FPLessEquals(Float64Literal(i), Float64Literal(j)), BooleanLiteral(i <= j))
    }

    for (i <- doubleValues) {
      check(s, FPUMinus(Float64Literal(i)), Float64Literal(-i))
      check(s, FPAbs(Float64Literal(i)), Float64Literal(Math.abs(i)))
      check(s, ToFloat(Float64Literal(i)), Float32Literal(i.toFloat))
      check(s, FPToBVJVM(11, 53, 32, Float64Literal(i)), Int32Literal(i.toInt))
      check(s, FPToBVJVM(11, 53, 64, Float64Literal(i)), Int64Literal(i.toLong))
      check(s, FPIsZero(Float64Literal(i)), BooleanLiteral(i == 0))
      check(s, FPIsNaN(Float64Literal(i)), BooleanLiteral(i.isNaN))
      check(s, FPIsInfinite(Float64Literal(i)), BooleanLiteral(i.isInfinite))
      check(s, FPIsNegative(Float64Literal(i)), BooleanLiteral(!i.isNaN && (i < 0 || 1 / i < 0)))
      check(s, FPIsPositive(Float64Literal(i)), BooleanLiteral(!i.isNaN && (i > 0 || 1 / i > 0)))
    }

    for (i <- Seq(Int8Literal(-3), Int16Literal(300), Int32Literal(Int.MaxValue), Int64Literal(Long.MaxValue))) {
      check(s, ToDouble(i), Float64Literal(i.toBigInt.toDouble))
      check(s, ToFloat(i), Float32Literal(i.toBigInt.toFloat))
    }
  }

  // Ties, values on either side of them, and their negations
  val roundingValues: Seq[Double] = Seq(2.5, -2.5, 0.5, -0.5, 1.4, -1.6)

  test("Floating Point Rounding", FloatingPoint) { ctx =>
    val s = solver(ctx)

    def rna(d: Double): Double = Math.copySign(Math.floor(Math.abs(d) + 0.5), d)
    def rtz(d: Double): Double = if (d < 0) Math.ceil(d) else Math.floor(d)
    val modes: Seq[(Expr, Double => Double)] = Seq(
      RoundNearestTiesToEven -> Math.rint,
      RoundNearestTiesToAway -> rna,
      RoundTowardPositive -> Math.ceil,
      RoundTowardNegative -> Math.floor,
      RoundTowardZero -> rtz,
    )

    for (d <- roundingValues; (rm, round) <- modes) {
      check(s, FPRound(rm, Float64Literal(d)), Float64Literal(round(d)))
      check(s, FPRound(rm, Float32Literal(d.toFloat)), Float32Literal(round(d.toFloat.toDouble).toFloat))
    }

    for (d <- roundingValues if d > 0) {
      check(s, Sqrt(RoundNearestTiesToEven, Float32Literal(d.toFloat)), Float32Literal(Math.sqrt(d.toFloat.toDouble).toFloat))
    }
  }

  test("Floating Point Rounding, Conversions and Classification", FloatingPoint) { ctx =>
    val s = solver(ctx)
    val modes = Seq(RoundNearestTiesToEven, RoundNearestTiesToAway, RoundTowardZero, RoundTowardPositive, RoundTowardNegative)

    // the results of `fp.roundToIntegral` in each of `modes`
    val rounded: Seq[(Double, Seq[Double])] = Seq(
      2.5   -> Seq(2.0, 3.0, 2.0, 3.0, 2.0),
      -2.5  -> Seq(-2.0, -3.0, -2.0, -2.0, -3.0),
      1.7   -> Seq(2.0, 2.0, 1.0, 2.0, 1.0),
      -0.3  -> Seq(-0.0, -0.0, -0.0, -0.0, -1.0),
      0.5   -> Seq(0.0, 1.0, 0.0, 1.0, 0.0),
      1e300 -> Seq(1e300, 1e300, 1e300, 1e300, 1e300)
    )
    for ((d, results) <- rounded; (rm, r) <- modes zip results) {
      check(s, FPRound(rm, Float64Literal(d)), Float64Literal(r))
      check(s, FPRound(rm, Float32Literal(d.toFloat)), Float32Literal(r.toFloat))
    }

    check(s, FPToBV(32, true, RoundTowardZero, Float64Literal(-2.7)), Int32Literal(-2))
    check(s, FPToBV(32, true, RoundTowardNegative, Float32Literal(-2.2f)), Int32Literal(-3))
    check(s, FPToBV(8, false, RoundNearestTiesToAway, Float64Literal(2.5)), BVLiteral(false, 3, 8))
    check(s, FPToBV(8, false, RoundNearestTiesToEven, Float64Literal(255.4)), BVLiteral(false, 255, 8))

    // unsigned bit-vectors are converted by value, not by their signed reinterpretation
    check(s, FPCast(11, 53, RoundNearestTiesToEven, BVLiteral(false, 200, 8)), Float64Literal(200.0))
    check(s, FPCast(8, 24, RoundNearestTiesToEven, BVLiteral(false, BigInt(2).pow(32) - 1, 32)), Float32Literal(4294967295f))
    check(s, FPCast(11, 53, RoundNearestTiesToEven, Int8Literal(-56)), Float64Literal(-56.0))

    check(s, FPFromBinary(8, 24, Int32Literal(java.lang.Float.floatToIntBits(1.5f))), Float32Literal(1.5f))
    check(s, Sqrt(RoundNearestTiesToEven, Float32Literal(2f)), Float32Literal(math.sqrt(2.0).toFloat))

    val classified = Seq(1.0, 0.0, -0.0, Double.MinPositiveValue, -java.lang.Double.MIN_NORMAL, Double.MaxValue,
      Double.PositiveInfinity, Double.NaN)
    for (d <- classified) {
      val normal = !d.isNaN && !d.isInfinite && Math.abs(d) >= java.lang.Double.MIN_NORMAL
      val subnormal = d != 0 && Math.abs(d) < java.lang.Double.MIN_NORMAL
      check(s, FPIsNormal(Float64Literal(d)), BooleanLiteral(normal))
      check(s, FPIsSubnormal(Float64Literal(d)), BooleanLiteral(subnormal))
    }
    check(s, FPIsSubnormal(Float32Literal(Float.MinPositiveValue)), BooleanLiteral(true))
    check(s, FPIsNormal(Float32Literal(Float.MinPositiveValue)), BooleanLiteral(false))
  }

  test("Floating Point Conversions to Reals", FloatingPoint, Reals) { ctx =>
    val s = solver(ctx)

    check(s, FPToReal(Float64Literal(0.75)), FractionLiteral(3, 4))
    check(s, FPToReal(Float32Literal(-1.5f)), FractionLiteral(-3, 2))
    check(s, FPToReal(Float64Literal(-0.0)), FractionLiteral(0, 1))
    check(s, FPToReal(Float64Literal(1e20)), FractionLiteral(BigInt(10).pow(20), 1))
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

    for (i <- floatValues.filter(_ != 0)) {
      check(s, FPIsNegative(Float32Literal(i)), BooleanLiteral(i < 0))
    }
    check(s, FPIsNegative(Float32Literal(-0)), BooleanLiteral(true))
    check(s, FPIsNegative(Float32Literal(0)), BooleanLiteral(false))

    for (i <- floatValues.filter(_ != 0)) {
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
