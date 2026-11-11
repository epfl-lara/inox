/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._

class StringEncoder private(override val sourceProgram: Program)
                           (val stringBijection: Bijection[Seq[Int], sourceProgram.trees.Expr],
                            val theory: StringTheory[sourceProgram.trees.type])
  extends SimpleEncoder(
    sourceProgram,
    stringEnc(sourceProgram)(theory, stringBijection),
    stringDec(sourceProgram)(theory, stringBijection),
    theory.extraFunctions,
    theory.extraSorts
  )

/** Strings as lists of characters, which are unsigned bit-vectors of `charSize` bits whose values are at most
  * `maxChar`: models with larger characters are rejected.
  */
private class StringTheory[Trees <: ast.Trees](val trees: Trees, val maxChar: Int) {
  import trees._
  import trees.dsl._

  val charSize: Int = if (maxChar <= 0xFFFF) 16 else 18

  val StringID     = FreshIdentifier("String")
  val StringNilID  = FreshIdentifier("StringNil")
  val StringConsID = FreshIdentifier("StringCons")

  val head = FreshIdentifier("head")
  val tail = FreshIdentifier("tail")

  // Characters of 18 bits range up to 0x3FFFF, beyond the SMT-LIB characters: the invariant bounds them
  val InvID = FreshIdentifier("string_inv")
  val Inv = mkFunDef(InvID)()(_ => (
    Seq("s" :: ADTType(StringID, Seq.empty)), BooleanType(), { case Seq(s) =>
    s.is(StringConsID) ==> (s.getField(head) <= BVLiteral(false, maxChar, charSize))
  }))

  val stringSort = mkSort(StringID, (if (charSize == 16) Seq() else Seq(HasADTInvariant(InvID)))*)()(_ => Seq(
    (StringNilID, Seq()),
    (StringConsID, Seq(ValDef(head, BVType(false, charSize)), ValDef(tail, ADTType(StringID, Seq.empty))))
  ))

  val String     = T(StringID)()
  val StringNil  = C(StringNilID, Seq())
  val StringCons = C(StringConsID, Seq())

  val SizeID = FreshIdentifier("size")
  val Size = mkFunDef(SizeID)()(_ => (
    Seq("s" :: String),
    IntegerType(), { case Seq(s) =>
    if_ (s.is(StringConsID)) {
      E(BigInt(1)) + E(SizeID)(s.getField(tail))
    } else_ {
      E(BigInt(0))
    }
  }))

  val TakeID = FreshIdentifier("take")
  val Take = mkFunDef(TakeID)()(_ => (
    Seq("s" :: String, "i" :: IntegerType()),
    String, { case Seq(s, i) =>
    if_ (s.is(StringConsID) && i > E(BigInt(0))) {
      StringCons(
        s.getField(head),
        E(TakeID)(s.getField(tail), i - E(BigInt(1))))
    } else_ {
      StringNil()
    }
  }))

  val DropID = FreshIdentifier("drop")
  val Drop = mkFunDef(DropID)()(_ => (
    Seq("s" :: String, "i" :: IntegerType()),
    String, { case Seq(s, i) =>
    if_ (s.is(StringConsID) && i > E(BigInt(0))) {
      E(DropID)(s.getField(tail), i - E(BigInt(1)))
    } else_ {
      s
    }
  }))

  val SliceID = FreshIdentifier("slice")
  val Slice = mkFunDef(SliceID)()(_ => (
    Seq("s" :: String, "from" :: IntegerType(), "to" :: IntegerType()),
    String, { case Seq(s, from, to) =>
    // Like SMT-LIB's str.substr, a negative start gives the empty string
    if_ (from >= E(BigInt(0))) {
      Take(Drop(s, from), to - from)
    } else_ {
      StringNil()
    }
  }))

  val ConcatID = FreshIdentifier("concat")
  val Concat = mkFunDef(ConcatID)()(_ => (
    Seq("s1" :: String, "s2" :: String),
    String, { case Seq(s1, s2) =>
    if_ (s1.is(StringConsID)) {
      StringCons(
        s1.getField(head),
        E(ConcatID)(s1.getField(tail), s2))
    } else_ {
      s2
    }
  }))

  val extraFunctions = Seq(Size, Take, Drop, Slice, Concat) ++ (if (charSize == 16) Seq() else Seq(Inv))
  val extraSorts = Seq(stringSort)
}

def stringEnc(sourceProgram: Program)
             (theory: StringTheory[sourceProgram.trees.type],
              stringBijection: Bijection[Seq[Int], sourceProgram.trees.Expr]): transformers.TreeTransformer { val s: sourceProgram.trees.type; val t: sourceProgram.trees.type } = {
  class StringEnc extends theory.trees.ConcreteSelfTreeTransformer {

    import theory._
    import theory.trees._
    import theory.trees.dsl._

    override def transform(e: Expr): Expr = e match {
      case s: StringLiteral => convertFromString(s.value)
      case StringLength(a) => Size(transform(a)).copiedFrom(e)
      case StringConcat(a, b) => Concat(transform(a), transform(b)).copiedFrom(e)
      case SubString(a, start, end) =>
        Slice(transform(a), transform(start), transform(end)).copiedFrom(e)
      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case StringType() => String
      case _ => super.transform(tpe)
    }

    private def convertFromString(v: Seq[Int]): Expr = stringBijection.cachedB(v) {
      if (v.exists(_ > maxChar)) throw TheoryException("string with characters outside of the alphabet (see --strings-bmp)")
      v.foldRight(StringNil()){ case (char, l) => StringCons(BVLiteral(false, char, charSize), l) }
    }
  }
  new StringEnc
}

def stringDec(sourceProgram: Program)
             (theory: StringTheory[sourceProgram.trees.type],
              stringBijection: Bijection[Seq[Int], sourceProgram.trees.Expr]): transformers.TreeTransformer { val s: sourceProgram.trees.type; val t: sourceProgram.trees.type } = {
  class StringDec extends theory.trees.ConcreteSelfTreeTransformer {

    import theory._
    import theory.trees._
    import theory.trees.dsl._

    override def transform(e: Expr): Expr = e match {
      case cc @ ADT(StringNilID | StringConsID, Seq(), args) =>
        StringLiteral(convertToString(cc)).copiedFrom(cc)
      case FunctionInvocation(SizeID, Seq(), Seq(a)) =>
        StringLength(transform(a)).copiedFrom(e)
      case FunctionInvocation(ConcatID, Seq(), Seq(a, b)) =>
        StringConcat(transform(a), transform(b)).copiedFrom(e)
      case FunctionInvocation(SliceID, Seq(), Seq(a, from, to)) =>
        SubString(transform(a), transform(from), transform(to)).copiedFrom(e)
      case FunctionInvocation(TakeID, Seq(), Seq(FunctionInvocation(DropID, Seq(), Seq(a, start)), length)) =>
        val rstart = transform(start)
        SubString(transform(a), rstart, Plus(rstart, transform(length))).copiedFrom(e)
      case FunctionInvocation(TakeID, Seq(), Seq(a, length)) =>
        SubString(transform(a), IntegerLiteral(0), transform(length)).copiedFrom(e)
      case FunctionInvocation(DropID, Seq(), Seq(a, count)) =>
        val ra = transform(a)
        SubString(ra, transform(count), StringLength(ra)).copiedFrom(e)
      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case String => StringType()
      case _ => super.transform(tpe)
    }

    private def convertToString(e: Expr): Seq[Int] = stringBijection.cachedA(e)(e match {
      case ADT(StringConsID, Seq(), Seq(c @ BVLiteral(false, _, _), l)) if c.toBigInt <= maxChar =>
        c.toBigInt.toInt +: convertToString(l)
      case ADT(StringConsID, Seq(), Seq(c, _)) =>
        throw TheoryException(s"string character $c outside of the alphabet")
      case ADT(StringNilID, Seq(), Seq()) => Seq()
    })
  }
  new StringDec
}

object StringEncoder {
  /** Encodes the strings of `p`, whose characters are at most `maxChar` (see `optStringsBMP`). */
  def apply(p: Program, maxChar: Int): StringEncoder { val sourceProgram: p.type } = {
    class Impl(override val sourceProgram: p.type)
              (override val stringBijection: Bijection[Seq[Int], p.trees.Expr],
               override val theory: StringTheory[p.trees.type])
      extends StringEncoder(sourceProgram)(stringBijection, theory)
    val stringBijection = new Bijection[Seq[Int], p.trees.Expr]()
    val theory = new StringTheory[p.trees.type](p.trees, maxChar)
    new Impl(p)(stringBijection, theory)
  }
}
