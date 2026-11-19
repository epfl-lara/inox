/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package evaluators

/** IEEE 754 floating point of any format and with every rounding mode, computed exactly.
  *
  * A number of `e` exponent bits and `s` significand bits (the hidden bit included, as in SMT-LIB)
  * is held as its `e + s` bits, in IEEE 754's layout: the sign, then the biased exponent, then the
  * fraction. There is a single NaN, the quiet NaN with only the top fraction bit set, as in SMT-LIB
  * and on the JVM. Every operation that IEEE 754 defines as the rounding of an exact result computes
  * the exact result as a fraction, or for the square root as an integer square root with enough
  * bits, and rounds it with the rounding mode.
  *
  * The JVM's `Float` and `Double` operations round to nearest, ties to even: they agree with these
  * on that mode, and [[RecursiveEvaluator]] uses them then.
  */
private[evaluators] object FloatingPoint {

  enum Rounding {
    case NearestEven, NearestAway, TowardPositive, TowardNegative, TowardZero
  }
  import Rounding._

  /** A fraction `n / d`, with `d > 0`. */
  final case class Rational(n: BigInt, d: BigInt)

  private def pow2(k: Int): BigInt = BigInt(1) << k

  /** `n / d` times `2^p`. */
  private def scaled(n: BigInt, d: BigInt, p: Int): (BigInt, BigInt) =
    if (p < 0) (n, d << -p) else (n << p, d)

  private def floorDiv(a: Int, b: Int): Int = Math.floorDiv(a, b)

  /** The integer square root of `n >= 0`, by Newton's method from a power of two above it (Scala
    * Native's `BigInteger` has no `sqrt`). */
  private def isqrt(n: BigInt): BigInt =
    if (n.signum == 0) n
    else {
      var x = pow2((n.bitLength + 1) / 2)
      var y = (x + n / x) >> 1
      while (y < x) { x = y; y = (x + n / x) >> 1 }
      x
    }

  /** The integer `k` such that `2^k <= n / d < 2^(k+1)`, for `n, d > 0`. */
  private def ilog2(n: BigInt, d: BigInt): Int = {
    val k = n.bitLength - d.bitLength
    if (k < 0) { if ((n << -k) < d) k - 1 else k }
    else { if (n < (d << k)) k - 1 else k }
  }

  /** Whether to round the integer part `i` of a positive magnitude up: `c` compares the dropped
    * fraction with one half, and `inexact` says whether anything was dropped. */
  private def roundUp(rm: Rounding, neg: Boolean, i: BigInt, c: Int, inexact: Boolean): Boolean =
    inexact && (rm match {
      case NearestEven => c > 0 || (c == 0 && i.testBit(0))
      case NearestAway => c >= 0
      case TowardPositive => !neg
      case TowardNegative => neg
      case TowardZero => false
    })

  /** `n / d` rounded to an integer. */
  def roundToInteger(rm: Rounding, n: BigInt, d: BigInt): BigInt = {
    val neg = n < 0
    val (i, r) = n.abs /% d
    val m = i + (if (roundUp(rm, neg, i, (2 * r).compare(d).sign, r != 0)) 1 else 0)
    if (neg) -m else m
  }

  final case class Format(e: Int, s: Int) {
    val width: Int = e + s
    val bias: Int = (1 << (e - 1)) - 1
    val maxExp: BigInt = pow2(e) - 1
    private val hidden: BigInt = pow2(s - 1)

    def sign(x: BigInt): Boolean = x.testBit(width - 1)
    def exp(x: BigInt): BigInt = (x >> (s - 1)) & maxExp
    def frac(x: BigInt): BigInt = x & (hidden - 1)

    def isNaN(x: BigInt): Boolean = exp(x) == maxExp && frac(x) != 0
    def isInfinite(x: BigInt): Boolean = exp(x) == maxExp && frac(x) == 0
    def isZero(x: BigInt): Boolean = exp(x) == 0 && frac(x) == 0
    def isNormal(x: BigInt): Boolean = exp(x) != 0 && exp(x) != maxExp
    def isSubnormal(x: BigInt): Boolean = exp(x) == 0 && !isZero(x)
    def isNegative(x: BigInt): Boolean = !isNaN(x) && sign(x)
    def isPositive(x: BigInt): Boolean = !isNaN(x) && !sign(x)

    private def bits(neg: Boolean, be: BigInt, f: BigInt): BigInt =
      (if (neg) pow2(width - 1) else BigInt(0)) + (be << (s - 1)) + f

    val nan: BigInt = bits(false, maxExp, pow2(s - 2))
    def infinity(neg: Boolean): BigInt = bits(neg, maxExp, 0)
    def zero(neg: Boolean): BigInt = bits(neg, 0, 0)
    def canonical(x: BigInt): BigInt = if (isNaN(x)) nan else x

    /** The value of a finite `x`. */
    def toRational(x: BigInt): Rational = {
      val be = exp(x)
      val m = if (be == 0) frac(x) else frac(x) + hidden
      val k = (if (be == 0) 1 else be.toInt) - bias - (s - 1)
      val sm = if (sign(x)) -m else m
      if (k < 0) Rational(sm, pow2(-k)) else Rational(sm << k, 1)
    }

    private def overflow(rm: Rounding, neg: Boolean): BigInt = rm match {
      case NearestEven | NearestAway => infinity(neg)
      case TowardPositive if !neg => infinity(neg)
      case TowardNegative if neg => infinity(neg)
      case _ => bits(neg, maxExp - 1, hidden - 1)
    }

    /** The number of significand `m` and exponent `qe` (of its last bit), where `m` was rounded to
      * at most `s` bits, or to `2^s` when rounding carried. */
    private def pack(rm: Rounding, neg: Boolean, qe: Int, m: BigInt): BigInt = {
      val (m2, qe2) = if (m == pow2(s)) (hidden, qe + 1) else (m, qe)
      if (m2 == 0) zero(neg)
      else if (m2 < hidden) bits(neg, 0, m2)
      else {
        val be = qe2 + (s - 1) + bias
        if (be >= maxExp) overflow(rm, neg) else bits(neg, be, m2 - hidden)
      }
    }

    /** The nonzero `n / d` rounded to this format. */
    def round(rm: Rounding, n: BigInt, d: BigInt): BigInt = {
      val neg = n < 0
      val emin = 1 - bias
      val k = ilog2(n.abs, d)
      val qe = k.max(emin) - (s - 1)
      val (sn, sd) = scaled(n.abs, d, -qe)
      val (i, r) = sn /% sd
      pack(rm, neg, qe, i + (if (roundUp(rm, neg, i, (2 * r).compare(sd).sign, r != 0)) 1 else 0))
    }

    def fromRational(rm: Rounding, n: BigInt, d: BigInt): BigInt = if (n == 0) zero(false) else round(rm, n, d)

    def neg(x: BigInt): BigInt = if (isNaN(x)) nan else x.flipBit(width - 1)
    def abs(x: BigInt): BigInt = if (sign(x)) neg(x) else canonical(x)

    def add(rm: Rounding, x: BigInt, y: BigInt): BigInt =
      if (isNaN(x) || isNaN(y)) nan
      else if (isInfinite(x)) { if (isInfinite(y) && sign(x) != sign(y)) nan else x }
      else if (isInfinite(y)) y
      else {
        val (a, b) = (toRational(x), toRational(y))
        val n = a.n * b.d + b.n * a.d
        // an exact zero is +0, or -0 when rounding toward negative, unless both are zeros of the same sign
        if (n == 0) { if (isZero(x) && isZero(y) && sign(x) == sign(y)) x else zero(rm == TowardNegative) }
        else round(rm, n, a.d * b.d)
      }

    def sub(rm: Rounding, x: BigInt, y: BigInt): BigInt = add(rm, x, neg(y))

    def mul(rm: Rounding, x: BigInt, y: BigInt): BigInt = {
      val negative = sign(x) != sign(y)
      if (isNaN(x) || isNaN(y)) nan
      else if (isInfinite(x) || isInfinite(y)) { if (isZero(x) || isZero(y)) nan else infinity(negative) }
      else if (isZero(x) || isZero(y)) zero(negative)
      else {
        val (a, b) = (toRational(x), toRational(y))
        round(rm, a.n * b.n, a.d * b.d)
      }
    }

    def div(rm: Rounding, x: BigInt, y: BigInt): BigInt = {
      val negative = sign(x) != sign(y)
      if (isNaN(x) || isNaN(y) || (isInfinite(x) && isInfinite(y)) || (isZero(x) && isZero(y))) nan
      else if (isInfinite(x)) infinity(negative)
      else if (isInfinite(y)) zero(negative)
      else if (isZero(y)) infinity(negative)
      else if (isZero(x)) zero(negative)
      else {
        val (a, b) = (toRational(x), toRational(y))
        val (n, d) = (a.n * b.d, a.d * b.n)
        if (d < 0) round(rm, -n, -d) else round(rm, n, d)
      }
    }

    def fma(rm: Rounding, x: BigInt, y: BigInt, z: BigInt): BigInt = {
      val negative = sign(x) != sign(y)
      if (isNaN(x) || isNaN(y) || isNaN(z)) nan
      else if (isInfinite(x) || isInfinite(y)) {
        if (isZero(x) || isZero(y) || (isInfinite(z) && sign(z) != negative)) nan else infinity(negative)
      }
      else if (isInfinite(z)) z
      else {
        val (a, b, c) = (toRational(x), toRational(y), toRational(z))
        val d = a.d * b.d * c.d
        val n = a.n * b.n * c.d + c.n * a.d * b.d
        if (n == 0) {
          if ((isZero(x) || isZero(y)) && isZero(z) && sign(z) == negative) z
          else zero(rm == TowardNegative)
        } else round(rm, n, d)
      }
    }

    def sqrt(rm: Rounding, x: BigInt): BigInt =
      if (isNaN(x)) nan
      else if (isZero(x)) x
      else if (sign(x)) nan
      else if (isInfinite(x)) x
      else {
        val Rational(n, d) = toRational(x)
        val k = floorDiv(ilog2(n, d), 2)
        val qe = k.max(1 - bias) - (s - 1)
        // the square root with one more bit than the significand, and whether more were dropped
        val (sn, sd) = scaled(n, d, 2 - 2 * qe)
        val (m, rest) = sn /% sd
        val t = isqrt(m)
        val (i, half) = (t >> 1, t.testBit(0))
        val sticky = rest != 0 || t * t != m
        val c = if (half) (if (sticky) 1 else 0) else -1
        pack(rm, false, qe, i + (if (roundUp(rm, false, i, c, half || sticky)) 1 else 0))
      }

    def roundToIntegral(rm: Rounding, x: BigInt): BigInt =
      if (isNaN(x) || isInfinite(x) || isZero(x)) canonical(x)
      else {
        val Rational(n, d) = toRational(x)
        val m = roundToInteger(rm, n, d)
        if (m == 0) zero(sign(x)) else round(rm, m, 1)
      }

    /** Compares two numbers that aren't NaN. */
    def compare(x: BigInt, y: BigInt): Int =
      if (isInfinite(x)) { if (isInfinite(y) && sign(x) == sign(y)) 0 else if (sign(x)) -1 else 1 }
      else if (isInfinite(y)) { if (sign(y)) 1 else -1 }
      else {
        val (a, b) = (toRational(x), toRational(y))
        (a.n * b.d).compare(b.n * a.d).sign
      }

    def equal(x: BigInt, y: BigInt): Boolean = !isNaN(x) && !isNaN(y) && compare(x, y) == 0
    def lessThan(x: BigInt, y: BigInt): Boolean = !isNaN(x) && !isNaN(y) && compare(x, y) < 0
    def lessEquals(x: BigInt, y: BigInt): Boolean = !isNaN(x) && !isNaN(y) && compare(x, y) <= 0

    /** `max` and `min` ignore a NaN operand unless both are NaN, and order `-0` below `+0`. */
    def max(x: BigInt, y: BigInt, isMax: Boolean): BigInt =
      if (isNaN(x)) canonical(y)
      else if (isNaN(y)) x
      else if (isZero(x) && isZero(y)) { if (isMax == sign(x)) y else x }
      else if (isMax == (compare(x, y) < 0)) y else x

    /** `x` rounded to an integer, saturated at `lo` and `hi`, with NaN converting to zero. */
    def toInteger(rm: Rounding, x: BigInt, lo: BigInt, hi: BigInt): BigInt =
      if (isNaN(x)) 0
      else if (isInfinite(x)) { if (sign(x)) lo else hi }
      else {
        val Rational(n, d) = toRational(x)
        roundToInteger(rm, n, d).max(lo).min(hi)
      }

    /** `x` of the format `from` in this one. */
    def cast(rm: Rounding, from: Format, x: BigInt): BigInt =
      if (from.isNaN(x)) nan
      else if (from.isInfinite(x)) infinity(from.sign(x))
      else if (from.isZero(x)) zero(from.sign(x))
      else {
        val Rational(n, d) = from.toRational(x)
        round(rm, n, d)
      }
  }
}
