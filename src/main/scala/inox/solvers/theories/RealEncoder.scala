/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

class RealEncoder private(override val sourceProgram: Program)
                         (theory: RealTheory[sourceProgram.trees.type])
  extends SimpleEncoder(
    sourceProgram,
    realEnc(sourceProgram)(theory),
    realDec(sourceProgram)(theory),
    theory.extraFunctions,
    theory.extraSorts
  )

private class RealTheory[Trees <: ast.Trees](val trees: Trees) {
  import trees._
  import trees.dsl._

  val num = FreshIdentifier("num")
  val denom = FreshIdentifier("denom")
  val fractionID = FreshIdentifier("fraction")

  // Denominators are kept strictly positive so that comparisons can be encoded
  // by cross-multiplication without having to account for signs.
  val fraction_inv = mkFunDef(FreshIdentifier("fraction_inv"))()(_ => (
    Seq("x" :: T(fractionID)()), BooleanType(), { case Seq(x) =>
    x.getField(denom) > E(BigInt(0))
  }))

  val fraction_eq = mkFunDef(FreshIdentifier("fraction_eq"))()(_ => (
    Seq("i1" :: T(fractionID)(), "i2" :: T(fractionID)()), BooleanType(), { case Seq(i1, i2) =>
    (i1.getField(num) * i2.getField(denom)) === (i1.getField(denom) * i2.getField(num))
  }))

  // Fractions are not normalized, so equality must be checked by cross-multiplication
  // (e.g. 1/2 == 2/4) rather than structurally.
  val fraction = mkSort(fractionID, HasADTInvariant(fraction_inv.id), HasADTEquality(fraction_eq.id))()(_ => Seq(
    (fractionID.freshen, Seq(ValDef(num, IntegerType()), ValDef(denom, IntegerType())))
  ))

  val fractionCons = fraction.constructors.head

  // Division by zero yields an unspecified value that only depends on the dividend, as in
  // SMT-LIB. As fractions are not normalized, this function may give different results for
  // different representations of the same dividend, which only adds models.
  val divByZero = mkFunDef(FreshIdentifier("div_by_zero"))()(_ => (
    Seq("x" :: T(fractionID)()), T(fractionID)(), { case Seq(_) =>
    choose("r" :: T(fractionID)())(_ => E(true))
  }))

  val extraFunctions = Seq(fraction_inv, fraction_eq, divByZero)
  val extraSorts = Seq(fraction)
}
def realEnc(sourceProgram: Program)
           (theory: RealTheory[sourceProgram.trees.type]): transformers.TreeTransformer { val s: sourceProgram.trees.type; val t: sourceProgram.trees.type } = {
  class RealEnc extends theory.trees.ConcreteSelfTreeTransformer {
    import theory._
    import theory.trees._
    import theory.trees.dsl._
    import sourceProgram.symbols.{given, _}

    protected def fields(e: Expr): (Expr, Expr) = {
      val te = transform(e)
      (te.getField(num), te.getField(denom))
    }

    override def transform(e: Expr): Expr = e match {
      case fl @ FractionLiteral(num, denom) if denom != 0 =>
        val FractionLiteral(n, d) = exprOps.normalizeFraction(fl)
        fractionCons(E(n), E(d))

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
        dsl.let("x" :: fraction(), transform(i1)) { x =>
          val ((ni1, di1), (ni2, di2)) = ((x.getField(num), x.getField(denom)), fields(i2))
          // The sign of the divisor's numerator must be moved to the numerator
          // in order to keep the denominator positive.
          dsl.let("n" :: IntegerType(), ni1 * di2) { n =>
            dsl.let("d" :: IntegerType(), di1 * ni2) { d =>
              if_ (d < E(BigInt(0))) {
                fractionCons(-n, -d)
              } else_ {
                if_ (d === E(BigInt(0))) {
                  E(divByZero.id)(x)
                } else_ {
                  fractionCons(n, d)
                }
              }
            }
          }
        }

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
  new RealEnc
}

def realDec(sourceProgram: Program)
           (theory: RealTheory[sourceProgram.trees.type]): transformers.TreeTransformer { val s: sourceProgram.trees.type; val t: sourceProgram.trees.type } = {
  class RealDec extends theory.trees.ConcreteSelfTreeTransformer {
    import theory._
    import theory.trees._
    import theory.trees.dsl._

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
  new RealDec
}

object RealEncoder {
  def apply(p: Program): RealEncoder { val sourceProgram: p.type } =
    new RealEncoder(p)(new RealTheory[p.trees.type](p.trees)).asInstanceOf
}
