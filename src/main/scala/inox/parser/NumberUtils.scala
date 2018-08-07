package inox
package parser

import scala.collection.BitSet

trait NumberUtils {
  def toFraction(whole: String, trailing: String, repeating: String): (BigInt, BigInt) = {

    type Fraction = (BigInt, BigInt)

    def add(a: Fraction, b: Fraction): Fraction = {
      val (na, da) = a
      val (nb, db) = b

      (na * db + nb * da, da * db)
    }

    def normalize(a: Fraction): Fraction = {
      val (na, da) = a

      val gcd = na.gcd(da)

      (na / gcd, da / gcd)
    }

    val t = BigInt(10).pow(trailing.length)

    val nonRepeatingPart: Fraction = (BigInt(whole + trailing), t)
    if (repeating.length == 0) {
      normalize(nonRepeatingPart)
    }
    else {
      val r = BigInt(10).pow(repeating.length)
      val sign = if (whole.startsWith("-")) -1 else 1
      val repeatingPart: Fraction = (sign * BigInt(repeating), (r - 1) * t)

      normalize(add(nonRepeatingPart, repeatingPart))
    }
  }

  def toBitSet(value: BigInt, base: Int): BitSet =
    inox.trees.BVLiteral(value, base).value // Ugly, but works...
}