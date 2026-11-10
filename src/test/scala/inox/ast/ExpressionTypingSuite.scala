/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

/** The types of expressions: those whose operands have the wrong types are [[Types.Untyped]]. */
class ExpressionTypingSuite extends AnyFunSuite {
  import inox.trees._

  given Symbols = NoSymbols

  val b = BooleanLiteral(true)
  val i = IntegerLiteral(1)
  val bv = Int32Literal(1)
  val f = Float32Literal(1.0f)
  val rm = RoundNearestTiesToEven
  val str = StringLiteral("s")
  val set = FiniteSet(Seq(i), IntegerType())
  val bag = FiniteBag(Seq(i -> i), IntegerType())
  val map = FiniteMap(Seq(), i, IntegerType(), IntegerType())

  private def untyped(es: Expr*): Unit =
    for (e <- es) assert(e.getType == Untyped, s"for $e")

  test("Core expressions") {
    untyped(
      Application(i, Seq(i)),
      IfExpr(i, i, i),
      IfExpr(b, i, b),
      Assume(i, i),
      Let(ValDef.fresh("x", IntegerType()), b, i),
      Equals(i, b),
      And(Seq(b, i)),
      Or(Seq(b, i)),
      Implies(i, b),
      Not(i),
      Tuple(Seq(i, Error(Untyped, "untyped"))),
      TupleSelect(i, 1),
      TupleSelect(Tuple(Seq(i, b)), 3),
      FunctionInvocation(FreshIdentifier("unknown"), Seq(), Seq()),
      ADTSelector(i, FreshIdentifier("field")),
      IsConstructor(i, FreshIdentifier("cons")),
    )
  }

  test("Arithmetic and comparisons") {
    untyped(
      Plus(i, b), Minus(i, bv), Times(b, b), Division(str, str), Remainder(i, bv), Modulo(b, b), UMinus(b),
      LessThan(b, b), GreaterThan(i, bv), LessEquals(str, str), GreaterEquals(b, i),
      StringConcat(str, i), SubString(str, b, i), StringLength(i),
    )
  }

  test("Bit-vector operations") {
    untyped(
      BVNot(i), BVAnd(i, i), BVOr(bv, i), BVXor(b, b), BVShiftLeft(i, bv), BVAShiftRight(i, i), BVLShiftRight(b, bv),
      BVNarrowingCast(i, Int8Type()), BVNarrowingCast(Int8Literal(1), Int32Type()),
      BVWideningCast(i, Int64Type()), BVWideningCast(Int64Literal(1), Int32Type()),
      BVUnsignedToSigned(i), BVUnsignedToSigned(bv),
      BVSignedToUnsigned(i), BVSignedToUnsigned(BVLiteral(false, 1, 32)),
      BVToInt(i), IntToBV(32, true, bv), IntToBV(0, true, i),
    )
  }

  test("Floating point operations") {
    untyped(
      FPEquals(f, i), FPAdd(rm, f, i), FPAdd(i, f, f), FPSub(i, f, f), FPUMinus(i), FPFMA(i, f, f, f),
      FPMul(i, f, f), FPDiv(i, f, f), FPAbs(i), FPMax(f, i), FPMin(i, f), FPRound(i, f), Sqrt(i, f),
      FPCast(8, 24, i, f), FPCast(8, 24, rm, b), FPFromBinary(8, 24, i), FPToBV(32, true, i, f), FPToBV(32, true, rm, i),
      FPToReal(i), FPLessThan(f, i), FPGreaterThan(i, f), FPLessEquals(f, b), FPGreaterEquals(b, f),
      FPIsZero(i), FPIsInfinite(i), FPIsNaN(i), FPIsNegative(i), FPIsPositive(i), FPIsNormal(i), FPIsSubnormal(i),
    )
  }

  test("Collections") {
    untyped(
      FiniteSet(Seq(b), IntegerType()), SetAdd(i, i), SetAdd(set, b), ElementOfSet(b, set), ElementOfSet(i, i),
      SubsetOf(set, i), SubsetOf(i, i), SetIntersection(set, bag), SetUnion(i, set), SetDifference(set, b),
      FiniteBag(Seq(b -> i), IntegerType()), BagAdd(i, i), BagAdd(bag, b), MultiplicityInBag(i, i),
      MultiplicityInBag(b, bag), BagIntersection(bag, set), BagUnion(i, i), BagDifference(bag, i),
      FiniteMap(Seq(b -> i), i, IntegerType(), IntegerType()), MapApply(i, i), MapApply(map, b),
      MapUpdated(i, i, i), MapUpdated(map, i, b), MapMerge(i, map, map), MapMerge(set, map, i),
    )
  }

  test("Typed expressions") {
    val x = ValDef.fresh("x", IntegerType())
    val l = Lambda(Seq(x), Plus(x.toVariable, i))
    assert(l.withParamSubst(Seq(IntegerLiteral(2)), x.toVariable) == IntegerLiteral(2))
    assert(StringLiteral.unapply(str) == Some("s"))
    assert(Float32Literal.unapply(i).isEmpty)
    assert(Float64Literal.unapply(f).isEmpty)
    assert(Float64Literal.unapply(Float64Literal(2.5)) == Some(2.5))
  }
}
