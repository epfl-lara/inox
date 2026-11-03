/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

/** Encodes Inox strings, whose characters are 16-bit UTF-16 code units, into strings
  * over 8-bit characters: each character `c` is represented by the two characters
  * `c >> 8` and `c & 0xFF`. The encoded strings are wrapped in an ADT whose invariant
  * ensures that their length is even.
  *
  * Note that the encoded string literals contain actual characters (not escape
  * sequences), so the solver target is responsible for escaping them.
  */
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

  private[theories] def encodeString(s: String): String =
    s.flatMap(c => new String(Array((c >> 8).toChar, (c & 0xFF).toChar)))

  private[theories] def decodeString(s: String): String = {
    if (s.length % 2 != 0) throw TheoryException(s"Can't decode string of odd length ${s.length}")
    s.grouped(2).map { pair =>
      val (hi, lo) = (pair.charAt(0), pair.charAt(1))
      if (hi > 0xFF || lo > 0xFF) throw TheoryException(s"Can't decode character pair ${hi.toInt}, ${lo.toInt}")
      ((hi << 8) | lo).toChar
    }.mkString
  }
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
      case StringLiteral(v) => stringCons(StringLiteral(ASCIIStringEncoder.encodeString(v)))
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
        StringLiteral(ASCIIStringEncoder.decodeString(s))

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
