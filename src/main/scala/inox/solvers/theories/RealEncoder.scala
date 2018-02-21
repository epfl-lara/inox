/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package theories

trait RealEncoder extends SimpleEncoder {
  import trees._
  import trees.dsl._

  private val num = FreshIdentifier("num")
  private val denom = FreshIdentifier("denom")
  private val fractionID = FreshIdentifier("fraction")

  private val fraction_inv = mkFunDef(FreshIdentifier("fraction_inv"))()(_ => (
    Seq("x" :: T(fractionID)()), BooleanType(), { case Seq(x) =>
      !(x.getField(denom) === E(BigInt(0)))
    }))

  private val fraction_eq = mkFunDef(FreshIdentifier("fraction_eq"))()(_ => (
    Seq("i1" :: T(fractionID)(), "i2" :: T(fractionID)()), BooleanType(), { case Seq(i1, i2) =>
      (i1.getField(num) * i2.getField(denom)) === (i1.getField(denom) * i2.getField(num))
    }))

  private val fraction = mkSort(fractionID)()(_ => Seq(
    (fractionID.freshen, Seq(ValDef(num, IntegerType()), ValDef(denom, IntegerType())))
  ))

  private val fractionCons = fraction.constructors.head

  override val extraFunctions = Seq(fraction_inv, fraction_eq)
  override val extraADTs = Seq(fraction)

  protected object encoder extends SelfTreeTransformer {
    import sourceProgram._

    protected def fields(e: Expr): (Expr, Expr) = {
      val te = transform(e)
      (te.getField(num), te.getField(denom))
    }

    override def transform(e: Expr): Expr = e match {
      case FractionLiteral(num, denom) => fractionCons(E(num), E(denom))

      case Plus(IsTyped(i1, RealType()), i2) =>
        val ((ni1, di1), (ni2, di2)) = (fields(i1), fields(i2))
        fractionCons(ni1 * di2 + ni2 * di1, di1 * di2)

      case Minus(IsTyped(i1, RealType()), i2) =>
        val ((ni1, di1), (ni2, di2)) = (fields(i1), fields(i2))
        fractionCons(ni1 * di2 - ni2 * di1, di1 * di2)

      case UMinus(IsTyped(i, RealType())) =>
        val (ni, di) = fields(i)
        fractionCons(- ni, di)

      case Times(IsTyped(i1, RealType()), i2) =>
        val ((ni1, di1), (ni2, di2)) = (fields(i1), fields(i2))
        fractionCons(ni1 * ni2, di1 * di2)

      case Division(IsTyped(i1, RealType()), i2) =>
        val ((ni1, di1), (ni2, di2)) = (fields(i1), fields(i2))
        fractionCons(ni1 * di2, di1 * ni2)

      case LessThan(IsTyped(i1, RealType()), i2) =>
        val ((ni1, di1), (ni2, di2)) = (fields(i1), fields(i2))
        ni1 * di2 < di1 * ni2

      case LessEquals(IsTyped(i1, RealType()), i2) =>
        val ((ni1, di1), (ni2, di2)) = (fields(i1), fields(i2))
        ni1 * di2 <= di1 * ni2

      case GreaterThan(IsTyped(i1, RealType()), i2) =>
        val ((ni1, di1), (ni2, di2)) = (fields(i1), fields(i2))
        ni1 * di2 > di1 * ni2

      case GreaterEquals(IsTyped(i1, RealType()), i2) =>
        val ((ni1, di1), (ni2, di2)) = (fields(i1), fields(i2))
        ni1 * di2 >= di1 * ni2

      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case RealType() => fraction()
      case _ => super.transform(tpe)
    }
  }

  protected object decoder extends SelfTreeTransformer {
    override def transform(e: Expr): Expr = e match {
      case ADT(id, Seq(), Seq(IntegerLiteral(num), IntegerLiteral(denom))) if id == fractionCons.id =>
        exprOps.normalizeFraction(FractionLiteral(num, denom))
      case _ => super.transform(e)
    }

    override def transform(tpe: Type): Type = tpe match {
      case ADTType(`fractionID`, Seq()) => RealType()
      case _ => super.transform(tpe)
    }
  }
}

object RealEncoder {
  def apply(p: Program): RealEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
  } with RealEncoder
}
