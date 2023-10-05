/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._
import utils.StringUtils._

class ASCIIStringEncoder private(override val sourceProgram: Program)
                                (theory: ASCIIStringTheory[sourceProgram.trees.type])
  extends SimpleEncoder(
    sourceProgram,
    asciiStringEnc(sourceProgram.trees)(theory),
    asciiStringDec(sourceProgram.trees)(theory),
    theory.extraFunctions,
    theory.extraSorts)

object ASCIIStringEncoder {
  def apply(p: Program): ASCIIStringEncoder { val sourceProgram: p.type } =
    new ASCIIStringEncoder(p)(new ASCIIStringTheory(p.trees)).asInstanceOf
}

private class ASCIIStringTheory[Trees <: ast.Trees](val trees: Trees) {
  import trees._
  import trees.dsl._

  val value = FreshIdentifier("value")
  val inv = FreshIdentifier("inv")

  val stringSort = mkSort(FreshIdentifier("String"), HasADTInvariant(inv))()(_ => Seq(
    (FreshIdentifier("String"), Seq(ValDef(value, StringType())))
  ))
  val stringCons = stringSort.constructors.head
  val StringConsID = stringCons.id

  val String: ADTType = T(stringSort.id)()

  val invariant = mkFunDef(inv)()(_ => (
    Seq("s" :: String), BooleanType(), { case Seq(s) =>
    StringLength(s.getField(value)) % E(BigInt(2)) === E(BigInt(0))
  }))

  val extraFunctions = Seq(invariant)
  val extraSorts = Seq(stringSort)
}

def asciiStringEnc(trees: ast.Trees)(theory: ASCIIStringTheory[trees.type]): transformers.TreeTransformer { val s: trees.type; val t: trees.type } = {
  class ASCIIStringEnc extends trees.ConcreteSelfTreeTransformer {
    import trees._
    import trees.dsl._
    import theory._

    private val TWO = IntegerLiteral(2)

    override def transform(e: Expr): Expr = e match {
      case StringLiteral(v) =>
        stringCons(StringLiteral(v.flatMap(c => c.toString.getBytes("UTF-8").toSeq match {
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
  new ASCIIStringEnc
}

def asciiStringDec(trees: ast.Trees)(theory: ASCIIStringTheory[trees.type]): transformers.TreeTransformer { val s: trees.type; val t: trees.type } = {
  class ASCIIStringDec extends trees.ConcreteSelfTreeTransformer {
    import trees._
    import trees.dsl._
    import theory._

    private val TWO = IntegerLiteral(2)

    override def transform(e: Expr): Expr = e match {
      case ADT(StringConsID, Seq(), Seq(StringLiteral(s))) =>
        def unescape(s: String): String = if (s.isEmpty) s else (s match {
          case FirstBytes(b1, b2, s2) =>
            val h: String = if (0 <= b1 && b1 <= 127 && b1 == b2) {
              b1.toChar.toString
            } else if (0 <= b1 && b1 <= 127 && 0 <= b2 && b2 <= 127) {
              new java.lang.String(Seq(
                (0x00 | (b1 >> 1)).toByte,
                (((b1 & 1) << 7) | b2).toByte
              ).toArray, "UTF-8")
            } else if ((b1 & 0xE0) == 0xC0) {
              new java.lang.String(Seq(b1, b2).toArray, "UTF-8")
            } else {
              // hopefully these are rare!
              throw TheoryException(s"Can't decode character ${encodeByte(b1)}${encodeByte(b2)}")
            }
            h + unescape(s2)

          case _ =>
            throw TheoryException(s"Can't decode string $s")
        })

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
  new ASCIIStringDec
}

private object FirstBytes {
  def unapply(s: String): Option[(Byte, Byte, String)] = s match {
    case JavaEncoded(b1, JavaEncoded(b2, s2)) => Some((b1, b2, s2))
    case _ if s.isEmpty => None
    case _ => s.charAt(0).toString.getBytes("UTF-8").toSeq match {
      case Seq(_) if s.length == 1 => None
      case Seq(b1) => s.charAt(1).toString.getBytes("UTF-8").toSeq match {
        case Seq(b2) => Some((b1, b2, s.drop(2)))
        case _ => None
      }
      case Seq(b1, b2) =>
        val i1 = new java.lang.String(Seq(b1, b2).toArray, "UTF-8").charAt(0).toInt
        if ((i1 & 0xFFFFFFE0) == 0xC0) {
          if (s.length == 1) None else s.charAt(1).toString.getBytes("UTF-8").toSeq match {
            case Seq(b3, b4) =>
              val i2 = new java.lang.String(Seq(b3, b4).toArray, "UTF-8").charAt(0).toInt
              if ((i2 & 0xFFFFFFC0) == 0x80) Some((i1.toByte, i2.toByte, s.drop(2)))
              else None
            case _ => None
          }
        } else {
          Some((b1, b2, s.tail))
        }
    }
  }
}
