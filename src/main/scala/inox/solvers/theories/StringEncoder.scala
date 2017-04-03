/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._

trait StringEncoder extends SimpleEncoder {
  import trees._
  import trees.dsl._

  val stringID     = FreshIdentifier("String")
  val stringNilID  = FreshIdentifier("StringNil")
  val stringConsID = FreshIdentifier("StringCons")

  val head = FreshIdentifier("head")
  val tail = FreshIdentifier("tail")

  val stringADT     = mkSort(stringID)()(Seq(stringConsID, stringNilID))
  val stringNilADT  = mkConstructor(stringNilID)()(Some(stringID))(_ => Seq())
  val stringConsADT = mkConstructor(stringConsID)()(Some(stringID))(_ => Seq(
    ValDef(head, CharType), ValDef(tail, ADTType(stringID, Seq.empty))
  ))

  val String     : ADTType = T(stringID)()
  val StringNil  : ADTType = T(stringNilID)()
  val StringCons : ADTType = T(stringConsID)()

  val SizeID = FreshIdentifier("size")
  val Size = mkFunDef(SizeID)()(_ => (
    Seq("s" :: String),
    IntegerType, { case Seq(s) =>
      if_ (s.isInstOf(StringCons)) {
        E(BigInt(1)) + E(SizeID)(s.asInstOf(StringCons).getField(tail))
      } else_ {
        E(BigInt(0))
      }
    }))

  val TakeID = FreshIdentifier("take")
  val Take = mkFunDef(TakeID)()(_ => (
    Seq("s" :: String, "i" :: IntegerType),
    String, { case Seq(s, i) =>
      if_ (s.isInstOf(StringCons) && i > E(BigInt(0))) {
        StringCons(
          s.asInstOf(StringCons).getField(head),
          E(TakeID)(s.asInstOf(StringCons).getField(tail), i - E(BigInt(1))))
      } else_ {
        StringNil()
      }
    }))

  val DropID = FreshIdentifier("drop")
  val Drop = mkFunDef(DropID)()(_ => (
    Seq("s" :: String, "i" :: IntegerType),
    String, { case Seq(s, i) =>
      if_ (s.isInstOf(StringCons) && i > E(BigInt(0))) {
        E(DropID)(s.asInstOf(StringCons).getField(tail), i - E(BigInt(1)))
      } else_ {
        s
      }
    }))

  val SliceID = FreshIdentifier("slice")
  val Slice = mkFunDef(SliceID)()(_ => (
    Seq("s" :: String, "from" :: IntegerType, "to" :: IntegerType),
    String, { case Seq(s, from, to) => Take(Drop(s, from), to - from) }))

  val ConcatID = FreshIdentifier("concat")
  val Concat = mkFunDef(ConcatID)()(_ => (
    Seq("s1" :: String, "s2" :: String),
    String, { case Seq(s1, s2) =>
      if_ (s1.isInstOf(StringCons)) {
        StringCons(
          s1.asInstOf(StringCons).getField(head),
          E(ConcatID)(s1.asInstOf(StringCons).getField(tail), s2))
      } else_ {
        s2
      }
    }))

  override val extraFunctions = Seq(Size, Take, Drop, Slice, Concat)
  override val extraADTs = Seq(stringADT, stringNilADT, stringConsADT)

  private val stringBijection = new Bijection[String, Expr]()

  private def convertToString(e: Expr): String  = stringBijection.cachedA(e)(e match {
    case ADT(StringCons, Seq(CharLiteral(c), l)) => (if(c < 31) (c + 97).toChar else c) + convertToString(l)
    case ADT(StringNil, Seq()) => ""
  })

  private def convertFromString(v: String): Expr = stringBijection.cachedB(v) {
    v.toList.foldRight(StringNil()){ case (char, l) => StringCons(E(char), l) }
  }

  protected object encoder extends SelfTreeTransformer {
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
      case StringType => String
      case _ => super.transform(tpe)
    }
  }

  protected object decoder extends SelfTreeTransformer {
    override def transform(e: Expr): Expr = e match {
      case cc @ ADT(adt, args) if adt == StringNil || adt == StringCons =>
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
      case String | StringCons | StringNil => StringType
      case _ => super.transform(tpe)
    }
  }
}

object StringEncoder {
  def apply(p: Program): StringEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
  } with StringEncoder
}
