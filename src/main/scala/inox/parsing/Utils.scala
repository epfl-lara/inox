/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.collection.BitSet

object Utils {

  def traverse[A](xs: Seq[Option[A]]): Option[Seq[A]] = {
    val zero: Option[Seq[A]] = Some(Seq[A]())

    xs.foldRight(zero) {
      case (Some(x), Some(xs)) => Some(x +: xs)
      case _ => None
    }
  }

  def traverse[E, A](xs: Seq[Either[E, A]]): Either[Seq[E], Seq[A]] = {
    val zero: Either[Seq[E], Seq[A]] = Right(Seq[A]())

    xs.foldRight(zero) {
      case (Right(x), Right(xs)) => Right(x +: xs)
      case (Right(_), Left(es)) => Left(es)
      case (Left(e), Right(_)) => Left(Seq(e))
      case (Left(e), Left(es)) => Left(e +: es)
    }
  }

  def either[E, A, B, R](a: Either[Seq[E], A], b: Either[Seq[E], B])(f: (A, B) => R): Either[Seq[E], R] = {
    (a, b) match {
      case (Left(eas), Left(ebs)) => Left(eas ++ ebs)
      case (Left(eas), _) => Left(eas)
      case (_, Left(ebs)) => Left(ebs)
      case (Right(xa), Right(xb)) => Right(f(xa, xb))
    }
  }

  def plural(n: Int, s: String, p: String): String = {
    if (n == 1) s else p
  }

  def classify[A, B, C](xs: Seq[A])(f: A => Either[B, C]): (Seq[B], Seq[C]) = {
    val mapped = xs.map(f)
    val lefts = mapped.collect {
      case Left(x) => x
    }
    val rights = mapped.collect {
      case Right(x) => x
    }
    (lefts, rights)
  }

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
}