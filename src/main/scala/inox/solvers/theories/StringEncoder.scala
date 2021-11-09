/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._

class StringEncoder private(override val sourceProgram: Program)
                           (theory: StringTheory[sourceProgram.trees.type],
                            enc: StringEnc[sourceProgram.type],
                            dec: StringDec[sourceProgram.type])
  extends SimpleEncoder(
    sourceProgram,
    enc.asInstanceOf,
    dec.asInstanceOf,
    theory.extraFunctions,
    theory.extraSorts
  )

private class StringTheory[Trees <: ast.Trees](val trees: Trees) {
  import trees._
  import trees.dsl._

  val StringID     = FreshIdentifier("String")
  val StringNilID  = FreshIdentifier("StringNil")
  val StringConsID = FreshIdentifier("StringCons")

  val head = FreshIdentifier("head")
  val tail = FreshIdentifier("tail")

  val stringSort = mkSort(StringID)()(_ => Seq(
    (StringNilID, Seq()),
    (StringConsID, Seq(ValDef(head, CharType()), ValDef(tail, ADTType(StringID, Seq.empty))))
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
    String, { case Seq(s, from, to) => Take(Drop(s, from), to - from) }))

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

  val extraFunctions = Seq(Size, Take, Drop, Slice, Concat)
  val extraSorts = Seq(stringSort)
}

private class StringEnc[Prog <: Program]
  (val sourceProgram: Prog)
  (val theory: StringTheory[sourceProgram.trees.type],
   val stringBijection: Bijection[String, sourceProgram.trees.Expr])
  extends theory.trees.ConcreteSelfTreeTransformer {

  import theory._
  import theory.trees._
  import theory.trees.dsl._

  override def transform(e: Expr): Expr = e match {
    case StringLiteral(v) => convertFromString(v)
    case StringLength(a) => Size(transform(a)).copiedFrom(e)
    case StringConcat(a, b) => Concat(transform(a), transform(b)).copiedFrom(e)
    case SubString(a, start, Plus(start2, length)) if start == start2  =>
      Take(Drop(transform(a), transform(start)), transform(length)).copiedFrom(e)
    case SubString(a, start, end) =>
      Slice(transform(a), transform(start), transform(end)).copiedFrom(e)
    case _ => super.transform(e)
  }

  override def transform(tpe: Type): Type = tpe match {
    case StringType() => String
    case _ => super.transform(tpe)
  }

  private def convertFromString(v: String): Expr = stringBijection.cachedB(v) {
    v.toList.foldRight(StringNil()){ case (char, l) => StringCons(E(char), l) }
  }
}

private class StringDec[Prog <: Program]
  (val sourceProgram: Prog)
  (val theory: StringTheory[sourceProgram.trees.type],
   val stringBijection: Bijection[String, sourceProgram.trees.Expr])
  extends theory.trees.ConcreteSelfTreeTransformer {

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

  private def convertToString(e: Expr): String  = stringBijection.cachedA(e)(e match {
    // Do not call toString on the char but rather String.valueOf because toString messes things up with UTF-8 codepoints
    case ADT(StringConsID, Seq(), Seq(CharLiteral(c), l)) => java.lang.String.valueOf(if(c < 31) (c + 97).toChar else c) + convertToString(l)
    case ADT(StringNilID, Seq(), Seq()) => ""
  })
}

object StringEncoder {
  def apply(p: Program): StringEncoder { val sourceProgram: p.type } = {
    val stringBijection = new Bijection[String, p.trees.Expr]()
    val theory = new StringTheory[p.trees.type](p.trees)
    val enc = new StringEnc[p.type](p)(theory, stringBijection)
    val dec = new StringDec[p.type](p)(theory, stringBijection)
    // For some reason, we need to explicitly type `StringEncoder { val sourceProgram: p.type }` in the asInstanceOf,
    // otherwise it tries to cast the expression to Nothing (such problem does not arise in other cases!)
    (new StringEncoder(p)(theory, enc, dec)).asInstanceOf[StringEncoder { val sourceProgram: p.type }]
  }
}
