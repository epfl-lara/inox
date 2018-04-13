/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._
import utils.StringUtils._

trait ASCIIStringEncoder extends SimpleEncoder {
  import trees._
  import trees.dsl._

  val value = FreshIdentifier("value")
  val inv = FreshIdentifier("inv")

  val stringSort = mkSort(FreshIdentifier("String"))()(_ => Seq(
    (FreshIdentifier("String"), Seq(ValDef(value, StringType())))
  ))
  val stringCons = stringSort.constructors.head
  val StringConsID = stringCons.id

  val String: ADTType = T(stringSort.id)()

  val invariant = mkFunDef(inv, IsInvariantOf(stringSort.id))()(_ => (
    Seq("s" :: String), BooleanType(), { case Seq(s) =>
      StringLength(s.getField(value)) % E(BigInt(2)) === E(BigInt(0))
    }))

  override protected val extraFunctions = Seq(invariant)
  override protected val extraSorts = Seq(stringSort)

  private def decodeFirstByte(s: String): (Byte, String) = s match {
    case JavaEncoded(head, s2) => (head, s2)
    case _ => s.charAt(0).toString.getBytes.toSeq match {
      case Seq(b) => (b, s.tail)
      case Seq(b1, b2) => (b1, encodeByte(b2) + s.tail)
    }
  }

  private val TWO = IntegerLiteral(2)

  protected object encoder extends SelfTreeTransformer {
    override def transform(e: Expr): Expr = e match {
      case StringLiteral(v) =>
        stringCons(StringLiteral(v.flatMap(c => c.toString.getBytes.toSeq match {
          case Seq(b) if 32 <= b && b <= 127 => b.toChar.toString + b.toChar.toString
          case Seq(b) => encodeByte(b) + encodeByte(b)
          case Seq(b1, b2) => encodeByte(b1) + encodeByte(b2)
        })))
      case StringLength(a) => Division(StringLength(transform(a).getField(value)), TWO)
      case StringConcat(a, b) => stringCons(StringConcat(transform(a).getField(value), transform(b).getField(value)))
      case SubString(a, start, end) => stringCons(SubString(transform(a).getField(value), transform(start) * TWO, transform(end) * TWO))
      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case StringType() => String
      case _ => super.transform(tpe)
    }
  }

  protected object decoder extends SelfTreeTransformer {

    override def transform(e: Expr): Expr = e match {
      case ADT(StringConsID, Seq(), Seq(StringLiteral(s))) =>
        def unescape(s: String): String = if (s.isEmpty) s else {
            val (b1, s2) = decodeFirstByte(s)
            if (s2.isEmpty) throw TheoryException("String doesn't satisfy invariant")
            val (b2, s3) = decodeFirstByte(s2)
            val h: String = if (0 <= b1 && b1 <= 127 && b1 == b2) {
              b1.toChar.toString
            } else if (0 <= b1 && b1 <= 127 && 0 <= b2 && b2 <= 127) {
              new java.lang.String(Seq(
                (0x00 | (b1 >> 1)).toByte,
                (((b1 & 1) << 7) | b2).toByte
              ).toArray, "UTF-8")
            } else if ((b1 & 0xC0) != 0) {
              new java.lang.String(Seq(b1, b2).toArray, "UTF-8")
            } else {
              // hopefully these are rare!
              throw FatalError(s"Can't decode character ${encodeByte(b1)}${encodeByte(b2)}")
            }
            h + unescape(s3)
          }

        StringLiteral(unescape(s))

      case ADTSelector(a, `value`) => transform(a)

      case Division(StringLength(a), TWO) =>
        StringLength(transform(a))

      case ADT(StringConsID, Seq(), Seq(StringConcat(a, b))) =>
        StringConcat(transform(a), transform(b))

      case ADT(StringConsID, Seq(), Seq(SubString(a, Times(start, TWO), Times(end, TWO)))) =>
        SubString(transform(a), transform(start), transform(end))

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case String => StringType()
      case _ => super.transform(tpe)
    }
  }
}

object ASCIIStringEncoder {
  def apply(p: Program): ASCIIStringEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
  } with ASCIIStringEncoder
}
