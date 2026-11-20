/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package evaluators

import org.scalatest.funsuite.AnyFunSuite

import java.math.{BigDecimal => JBigDecimal, RoundingMode => JRoundingMode}

/** Checks [[FloatingPoint]] against the JVM's `Float` and `Double`, on special values and random ones.
  *
  * The JVM rounds to nearest, ties to even. For the other rounding modes, the expected result is the
  * neighbor of the JVM's result on the side of the exact one, or the JVM's result when it is exact.
  */
class FloatingPointSuite extends AnyFunSuite {
  import FloatingPoint._
  import Rounding._

  val modes = Seq(NearestEven, NearestAway, TowardPositive, TowardNegative, TowardZero)

  /** The JVM's view of a format. */
  abstract class Jvm[T](val f: Format, val name: String) {
    def toBits(x: T): BigInt
    def fromBits(x: BigInt): T
    def specials: Seq[T]
    def random(r: scala.util.Random): T
    def toDouble(x: T): Double
    def add(x: T, y: T): T
    def sub(x: T, y: T): T
    def mul(x: T, y: T): T
    def div(x: T, y: T): T
    def fma(x: T, y: T, z: T): T
    def sqrt(x: T): T
    def min(x: T, y: T): T
    def max(x: T, y: T): T
    def fromLong(l: Long): T
    def lt(x: T, y: T): Boolean
    def le(x: T, y: T): Boolean
    def eq(x: T, y: T): Boolean
    def minNormal: Double

    def values(seed: Int, n: Int): Seq[BigInt] = {
      val r = new scala.util.Random(seed)
      (specials ++ Seq.fill(n)(random(r))).map(toBits)
    }
  }

  object F64 extends Jvm[Double](Format(11, 53), "Float64") {
    def toBits(x: Double) = BigInt(java.lang.Double.doubleToRawLongBits(x)) & ((BigInt(1) << 64) - 1)
    def fromBits(x: BigInt) = java.lang.Double.longBitsToDouble(x.toLong)
    def specials = Seq(0.0, -0.0, 1.0, -1.0, 0.5, 1.5, 2.5, -2.5, 0.1, 1.0 / 3, 2.0 / 3, 1e308, -1e308,
      Double.MaxValue, -Double.MaxValue, Double.MinPositiveValue, -Double.MinPositiveValue,
      java.lang.Double.MIN_NORMAL, -java.lang.Double.MIN_NORMAL, java.lang.Double.MIN_NORMAL / 3,
      Double.PositiveInfinity, Double.NegativeInfinity, Double.NaN, 4503599627370496.5, 9007199254740993.0,
      1e18, -1e19, 1e300, 1e-300, Math.nextDown(1.0), Math.nextUp(1.0))
    def random(r: scala.util.Random) = r.nextInt(4) match {
      case 0 => java.lang.Double.longBitsToDouble(r.nextLong())
      case 1 => (r.nextInt(2001) - 1000) / 8.0
      case 2 => r.nextGaussian() * Math.pow(2, r.nextInt(80) - 40)
      case _ => Math.scalb(r.nextDouble(), r.nextInt(2200) - 1100) * (if (r.nextBoolean()) 1 else -1)
    }
    def toDouble(x: Double) = x
    def add(x: Double, y: Double) = x + y
    def sub(x: Double, y: Double) = x - y
    def mul(x: Double, y: Double) = x * y
    def div(x: Double, y: Double) = x / y
    def fma(x: Double, y: Double, z: Double) = Math.fma(x, y, z)
    def sqrt(x: Double) = Math.sqrt(x)
    def min(x: Double, y: Double) = Math.min(x, y)
    def max(x: Double, y: Double) = Math.max(x, y)
    def fromLong(l: Long) = l.toDouble
    def lt(x: Double, y: Double) = x < y
    def le(x: Double, y: Double) = x <= y
    def eq(x: Double, y: Double) = x == y
    def minNormal = java.lang.Double.MIN_NORMAL
  }

  object F32 extends Jvm[Float](Format(8, 24), "Float32") {
    def toBits(x: Float) = BigInt(java.lang.Float.floatToRawIntBits(x)) & ((BigInt(1) << 32) - 1)
    def fromBits(x: BigInt) = java.lang.Float.intBitsToFloat(x.toInt)
    def specials = Seq(0.0f, -0.0f, 1.0f, -1.0f, 0.5f, 1.5f, 2.5f, -2.5f, 0.1f, 1.0f / 3, 2.0f / 3, 1e38f,
      -1e38f, Float.MaxValue, -Float.MaxValue, Float.MinPositiveValue, -Float.MinPositiveValue,
      java.lang.Float.MIN_NORMAL, -java.lang.Float.MIN_NORMAL, java.lang.Float.MIN_NORMAL / 3,
      Float.PositiveInfinity, Float.NegativeInfinity, Float.NaN, 8388608.5f, 16777217.0f, 1e18f, -1e19f,
      Math.nextDown(1.0f), Math.nextUp(1.0f))
    def random(r: scala.util.Random) = r.nextInt(4) match {
      case 0 => java.lang.Float.intBitsToFloat(r.nextInt())
      case 1 => (r.nextInt(2001) - 1000) / 8.0f
      case 2 => (r.nextGaussian() * Math.pow(2, r.nextInt(40) - 20)).toFloat
      case _ => Math.scalb(r.nextFloat(), r.nextInt(300) - 150) * (if (r.nextBoolean()) 1 else -1)
    }
    def toDouble(x: Float) = x.toDouble
    def add(x: Float, y: Float) = x + y
    def sub(x: Float, y: Float) = x - y
    def mul(x: Float, y: Float) = x * y
    def div(x: Float, y: Float) = x / y
    def fma(x: Float, y: Float, z: Float) = Math.fma(x, y, z)
    def sqrt(x: Float) = Math.sqrt(x.toDouble).toFloat
    def min(x: Float, y: Float) = Math.min(x, y)
    def max(x: Float, y: Float) = Math.max(x, y)
    def fromLong(l: Long) = l.toFloat
    def lt(x: Float, y: Float) = x < y
    def le(x: Float, y: Float) = x <= y
    def eq(x: Float, y: Float) = x == y
    def minNormal = java.lang.Float.MIN_NORMAL.toDouble
  }

  /** A fraction `n / d` with `d > 0`, as the reference values. Fractions are much faster than
    * `BigDecimal`s here, whose decimal expansion of `2^-1074` has hundreds of digits. */
  final case class Q(n: BigInt, d: BigInt) {
    def add(o: Q) = Q(n * o.d + o.n * d, d * o.d)
    def subtract(o: Q) = Q(n * o.d - o.n * d, d * o.d)
    def multiply(o: Q) = Q(n * o.n, d * o.d)
    def divide(o: Q) = if (o.n < 0) Q(-n * o.d, d * -o.n) else Q(n * o.d, d * o.n)
    def abs = Q(n.abs, d)
    def signum = n.signum
    def compareTo(o: Q): Int = (n * o.d).compare(o.n * d).sign
    def toBigDecimal = new JBigDecimal(n.bigInteger).divide(new JBigDecimal(d.bigInteger))
  }

  /** The exact value of a finite `x`. */
  def exact(f: Format, x: BigInt): Q = {
    val Rational(n, d) = f.toRational(x)
    Q(n, d)
  }

  /** The next number of `f` above `x`, which isn't NaN. */
  def nextUp(f: Format, x: BigInt): BigInt =
    if (f.isInfinite(x) && !f.sign(x)) x
    else if (f.isZero(x)) BigInt(1)
    else if (f.sign(x)) x - 1
    else x + 1

  def nextDown(f: Format, x: BigInt): BigInt = f.neg(nextUp(f, f.neg(x)))

  /** Compares `x`, which may be infinite, with `q`. */
  def compareTo(f: Format, x: BigInt, q: Q): Int =
    if (f.isInfinite(x)) { if (f.sign(x)) -1 else 1 }
    else exact(f, x).compareTo(q).sign

  /** The exact `q` rounded with `rm`, given `n`, the JVM's rounding of it to nearest, ties to even. */
  def expected(f: Format, rm: Rounding, n: BigInt, q: Q): BigInt = {
    val c = compareTo(f, n, q)
    rm match {
      case NearestEven => n
      case TowardPositive => if (c >= 0) n else nextUp(f, n)
      case TowardNegative => if (c <= 0) n else nextDown(f, n)
      case TowardZero => if (c == 0) n else expected(f, if (q.signum > 0) TowardNegative else TowardPositive, n, q)
      case NearestAway =>
        if (c == 0 || f.isInfinite(n)) n
        else {
          val other = if (c > 0) nextDown(f, n) else nextUp(f, n)
          val tie = !f.isInfinite(other) &&
            exact(f, n).subtract(q).abs.compareTo(exact(f, other).subtract(q).abs) == 0
          if (tie && exact(f, other).abs.compareTo(exact(f, n).abs) > 0) other else n
        }
    }
  }

  def same(f: Format, actual: BigInt, expected: BigInt, what: => String): Unit =
    assert(actual == f.canonical(expected), s"$what: got ${actual.toString(16)}, expected ${expected.toString(16)}")

  def isFinite(f: Format, x: BigInt) = !f.isNaN(x) && !f.isInfinite(x)

  /** Checks an operation in every rounding mode, where `q` is its exact result when it is finite and
    * nonzero, and `zero` the expected result in the given mode when the exact result is zero. */
  def checkRounded(f: Format, what: => String, n: BigInt, q: Option[Q], zero: Rounding => BigInt)
                  (op: Rounding => BigInt): Unit =
    for (rm <- modes) q match {
      case Some(q) if q.signum == 0 => same(f, op(rm), zero(rm), s"$what in $rm")
      case Some(q) => same(f, op(rm), expected(f, rm, n, q), s"$what in $rm")
      case None => same(f, op(rm), n, s"$what in $rm")
    }

  def checkFormat[T](jvm: Jvm[T]): Unit = {
    import jvm.{f, fromBits, toBits}
    val xs = jvm.values(1, 100)
    val ys = jvm.values(2, 100)

    test(s"${jvm.name} classification, sign and comparison agree with the JVM") {
      for (x <- xs) {
        val d = jvm.toDouble(fromBits(x))
        assert(f.isNaN(x) == d.isNaN)
        assert(f.isInfinite(x) == d.isInfinite)
        assert(f.isZero(x) == (d == 0))
        assert(f.isSubnormal(x) == (d != 0 && Math.abs(d) < jvm.minNormal))
        assert(f.isNormal(x) == (!d.isNaN && !d.isInfinite && Math.abs(d) >= jvm.minNormal))
        assert(f.isNegative(x) == (!d.isNaN && f.sign(x)))
        assert(f.isPositive(x) == (!d.isNaN && !f.sign(x)))
        same(f, f.neg(x), toBits(fromBits(f.neg(x))), "neg")
        assert(f.neg(f.neg(x)) == f.canonical(x))
        same(f, f.abs(x), f.canonical(x).clearBit(f.width - 1), "abs")
        if (isFinite(f, x)) assert(exact(f, x).toBigDecimal.compareTo(new JBigDecimal(d)) == 0)
        for (y <- ys.take(60)) {
          val (a, b) = (fromBits(x), fromBits(y))
          assert(f.lessThan(x, y) == jvm.lt(a, b))
          assert(f.lessEquals(x, y) == jvm.le(a, b))
          assert(f.equal(x, y) == jvm.eq(a, b))
          // a NaN operand is ignored, unlike on the JVM
          val (mx, mn) =
            if (f.isNaN(x)) (y, y) else if (f.isNaN(y)) (x, x)
            else (toBits(jvm.max(a, b)), toBits(jvm.min(a, b)))
          same(f, f.max(x, y, true), mx, "max")
          same(f, f.max(x, y, false), mn, "min")
        }
      }
    }

    test(s"${jvm.name} addition, subtraction, multiplication and division in every rounding mode") {
      for (x <- xs; y <- ys) {
        val (a, b) = (fromBits(x), fromBits(y))
        val finite = isFinite(f, x) && isFinite(f, y)
        def q(r: (Q, Q) => Q) = if (finite) Some(r(exact(f, x), exact(f, y))) else None
        // an exact zero sum is -0 when rounding toward negative, unless both operands are +0
        def zeroSum(sx: Boolean, sy: Boolean)(rm: Rounding) =
          if (f.isZero(x) && f.isZero(y) && sx == sy) f.zero(sx) else f.zero(rm == TowardNegative)
        checkRounded(f, s"$a + $b", toBits(jvm.add(a, b)), q((a, b) => a.add(b)),
          zeroSum(f.sign(x), f.sign(y)))(f.add(_, x, y))
        checkRounded(f, s"$a - $b", toBits(jvm.sub(a, b)), q((a, b) => a.subtract(b)),
          zeroSum(f.sign(x), !f.sign(y)))(f.sub(_, x, y))
        val signs = f.sign(x) != f.sign(y)
        checkRounded(f, s"$a * $b", toBits(jvm.mul(a, b)), q((a, b) => a.multiply(b)), _ => f.zero(signs))(f.mul(_, x, y))
        val quotient = if (finite && !f.isZero(y)) Some(exact(f, x).divide(exact(f, y))) else None
        checkRounded(f, s"$a / $b", toBits(jvm.div(a, b)), quotient, _ => f.zero(signs))(f.div(_, x, y))
      }
    }

    test(s"${jvm.name} fused multiply-add in every rounding mode") {
      val zs = jvm.values(3, 20)
      for (x <- xs.take(40); y <- ys.take(40); z <- zs) {
        val (a, b, c) = (fromBits(x), fromBits(y), fromBits(z))
        val finite = isFinite(f, x) && isFinite(f, y) && isFinite(f, z)
        val q = if (finite) Some(exact(f, x).multiply(exact(f, y)).add(exact(f, z))) else None
        val productSign = f.sign(x) != f.sign(y)
        val productZero = f.isZero(x) || f.isZero(y)
        def zero(rm: Rounding) =
          if (productZero && f.isZero(z) && f.sign(z) == productSign) z else f.zero(rm == TowardNegative)
        checkRounded(f, s"fma($a, $b, $c)", toBits(jvm.fma(a, b, c)), q, zero)(f.fma(_, x, y, z))
      }
    }

    test(s"${jvm.name} square roots in every rounding mode") {
      for (x <- xs ++ ys) {
        val n = toBits(jvm.sqrt(fromBits(x)))
        for (rm <- modes) {
          val r = f.sqrt(rm, x)
          if (!isFinite(f, x) || f.isZero(x) || f.sign(x)) same(f, r, n, s"sqrt(${fromBits(x)})")
          else {
            // the square of the result brackets x as rounding requires
            val q = exact(f, x)
            val v = exact(f, r)
            val (lo, hi) = (exact(f, nextDown(f, r)), if (f.isInfinite(nextUp(f, r))) null else exact(f, nextUp(f, r)))
            val c = v.multiply(v).compareTo(q)
            rm match {
              case TowardPositive => assert(c >= 0 && lo.multiply(lo).compareTo(q) < 0)
              case TowardNegative | TowardZero => assert(c <= 0 && (hi == null || hi.multiply(hi).compareTo(q) > 0))
              case _ => same(f, r, n, s"sqrt(${fromBits(x)}) in $rm")
            }
          }
        }
      }
    }

    test(s"${jvm.name} rounding to integers in every rounding mode") {
      val jmodes = Map(NearestEven -> JRoundingMode.HALF_EVEN, NearestAway -> JRoundingMode.HALF_UP,
        TowardPositive -> JRoundingMode.CEILING, TowardNegative -> JRoundingMode.FLOOR, TowardZero -> JRoundingMode.DOWN)
      for (x <- xs ++ ys; rm <- modes) {
        val r = f.roundToIntegral(rm, x)
        if (!isFinite(f, x)) same(f, r, x, "roundToIntegral")
        else {
          val i = exact(f, x).toBigDecimal.setScale(0, jmodes(rm))
          assert(exact(f, r).toBigDecimal.compareTo(i) == 0, s"roundToIntegral($rm, ${fromBits(x)})")
          assert(f.sign(r) == f.sign(x))
        }
        val lo = -(BigInt(1) << 63)
        val hi = (BigInt(1) << 63) - 1
        val t = f.toInteger(rm, x, lo, hi)
        if (f.isNaN(x)) assert(t == 0)
        else if (f.isInfinite(x)) assert(t == (if (f.sign(x)) lo else hi))
        else assert(t == BigInt(exact(f, x).toBigDecimal.setScale(0, jmodes(rm)).toBigInteger).max(lo).min(hi))
        if (rm == TowardZero) assert(t == BigInt(jvm.toDouble(fromBits(x)).toLong))
      }
    }

    test(s"${jvm.name} conversions from integers and fractions in every rounding mode") {
      val r = new scala.util.Random(4)
      val ls = Seq(0L, 1L, -1L, Long.MaxValue, Long.MinValue, (1L << 53) + 1, (1L << 24) + 1, -(1L << 53) - 3) ++
        Seq.fill(300)(r.nextLong() >> r.nextInt(64))
      for (l <- ls) {
        checkRounded(f, s"$l", toBits(jvm.fromLong(l)), Some(Q(l, 1)), _ => f.zero(false))(f.fromRational(_, l, 1))
      }
      for (_ <- 1 to 300) {
        val n = BigInt(r.nextLong()) << r.nextInt(100)
        val d = BigInt(r.nextLong()).abs + 1
        for (rm <- modes) {
          val x = f.fromRational(rm, n, d)
          val q = Q(n, d)
          if (isFinite(f, x)) {
            val c = exact(f, x).compareTo(q)
            rm match {
              case TowardPositive => assert(c >= 0 && compareTo(f, nextDown(f, x), q) < 0)
              case TowardNegative => assert(c <= 0 && compareTo(f, nextUp(f, x), q) > 0)
              case _ =>
            }
          }
        }
      }
    }
  }

  checkFormat(F64)
  checkFormat(F32)

  test("Conversions between Float32, Float64 and half precision in every rounding mode") {
    val half = Format(5, 11)
    for (x <- F64.values(5, 3000)) {
      val d = F64.fromBits(x)
      val q = if (isFinite(F64.f, x)) Some(exact(F64.f, x)) else None
      checkRounded(F32.f, s"$d.toFloat", F32.toBits(d.toFloat), q, _ => F32.f.zero(F64.f.sign(x)))(F32.f.cast(_, F64.f, x))
      // a cast to half precision and back to Float64 rounds once, as the cast of Float64 to half does
      for (rm <- modes) {
        val h = half.cast(rm, F64.f, x)
        if (isFinite(F64.f, x) && isFinite(half, h) && !half.isZero(h)) {
          val c = exact(half, h).compareTo(q.get)
          rm match {
            case TowardPositive => assert(c >= 0 && compareTo(half, nextDown(half, h), q.get) < 0)
            case TowardNegative => assert(c <= 0 && compareTo(half, nextUp(half, h), q.get) > 0)
            case _ =>
          }
        }
        same(F64.f, F64.f.cast(rm, half, h), F64.f.cast(NearestEven, half, h), "half to Float64 is exact")
      }
    }
    for (x <- F32.values(6, 3000); rm <- modes) {
      same(F64.f, F64.f.cast(rm, F32.f, x), F64.toBits(F32.fromBits(x).toDouble), s"${F32.fromBits(x)}.toDouble")
    }
  }
}
