/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._

import org.apache.commons.lang3.StringEscapeUtils

trait ASCIIStringEncoder extends SimpleEncoder {
  import trees._
  import trees.dsl._

  val value = FreshIdentifier("value")
  val inv = FreshIdentifier("inv")

  val stringADT = mkConstructor(
    FreshIdentifier("String"), HasADTInvariant(inv)
  )()(None)(_ => Seq(ValDef(value, StringType)))

  val String: ADTType = T(stringADT.id)()

  val invariant = mkFunDef(inv)()(_ => (
    Seq("s" :: String), BooleanType, { case Seq(s) =>
      StringLength(s.getField(value)) % E(BigInt(2)) === E(BigInt(0))
    }))

  override protected val extraFunctions = Seq(invariant)
  override protected val extraADTs = Seq(stringADT)

  private def toHex(i: Int): String = {
    if (0 <= i && i <= 9) i.toString else (i + 55).toChar.toString
  }

  private def fromHex(c: Char): Int = {
    if (c >= 'A' && c <= 'F') (c - 55).toInt
    else if (c >= 'a' && c <= 'f') (c - 87).toInt
    else c.toString.toInt
  }

  private def encodeByte(b: Byte): String = "\\x" + toHex((b >> 4) & 0xF) + toHex(b & 0xF)
  private def decodeHex(s: String): Byte = ((fromHex(s.charAt(2)) << 4) + fromHex(s.charAt(3))).toByte

  private val hex = """^\\x[0-9A-Fa-f]{2}""".r

  private def decodeFirstByte(s: String): (Byte, String) = {
    if (hex.findFirstIn(s).isDefined) {
      val (head, s2) = s.splitAt(4)
      (decodeHex(head), s2)
    } else if (s.charAt(0) == '\\') {
      val Seq(b) = StringEscapeUtils.unescapeJava(s.take(2)).getBytes.toSeq
      (b, s.drop(2))
    } else s.charAt(0).toString.getBytes.toSeq match {
      case Seq(b) => (b, s.tail)
      case Seq(b1, b2) => (b1, encodeByte(b2) + s.tail)
    }
  }

  private val TWO = IntegerLiteral(2)

  protected object encoder extends SelfTreeTransformer {
    override def transform(e: Expr): Expr = e match {
      case StringLiteral(v) =>
        String(StringLiteral(v.flatMap(c => c.toString.getBytes.toSeq match {
          case Seq(b) if 32 <= b && b <= 127 => b.toChar.toString + b.toChar.toString
          case Seq(b) => encodeByte(b) + encodeByte(b)
          case Seq(b1, b2) => encodeByte(b1) + encodeByte(b2)
        })))
      case StringLength(a) => Division(StringLength(transform(a).getField(value)), TWO)
      case StringConcat(a, b) => String(StringConcat(transform(a).getField(value), transform(b).getField(value)))
      case SubString(a, start, end) => String(SubString(transform(a).getField(value), transform(start) * TWO, transform(end) * TWO))
      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case StringType => String
      case _ => super.transform(tpe)
    }
  }

  protected object decoder extends SelfTreeTransformer {

    override def transform(e: Expr): Expr = e match {
      case ADT(String, Seq(StringLiteral(s))) =>
        def unescape(s: String): String = if (s.isEmpty) s else {
          val (b1, s2) = decodeFirstByte(s)
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

      case ADT(String, Seq(StringConcat(a, b))) =>
        StringConcat(transform(a), transform(b))

      case ADT(String, Seq(SubString(a, Times(start, TWO), Times(end, TWO)))) =>
        SubString(transform(a), transform(start), transform(end))

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case String => StringType
      case _ => super.transform(tpe)
    }
  }
}

object ASCIIStringEncoder {
  def apply(p: Program): ASCIIStringEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
  } with ASCIIStringEncoder
}
