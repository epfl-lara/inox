/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

class TypeOpsSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import dsl._

  val boxID = FreshIdentifier("Box")
  val boxConsID = FreshIdentifier("BoxCons")
  val box = mkSort(boxID)("A") { case Seq(a) => Seq((boxConsID, Seq(ValDef(FreshIdentifier("v"), a)))) }

  val symbols = NoSymbols.withSorts(Seq(box))
  given Symbols = symbols
  import symbols._

  val T = TypeParameter.fresh("T")
  val U = TypeParameter.fresh("U")
  def Box(t: Type) = ADTType(boxID, Seq(t))

  def positive(name: String) = {
    val vd = ValDef.fresh(name, IntegerType())
    RefinementType(vd, vd.toVariable > E(BigInt(0)))
  }
  def even(name: String) = {
    val vd = ValDef.fresh(name, IntegerType())
    RefinementType(vd, Equals(Modulo(vd.toVariable, E(BigInt(2))), E(BigInt(0))))
  }

  test("Bounds of unrelated and equal types") {
    assert(leastUpperBound(IntegerType(), IntegerType()) == IntegerType())
    assert(leastUpperBound(IntegerType(), BooleanType()) == Untyped)
    assert(leastUpperBound(Seq()) == Untyped)
    assert(greatestLowerBound(Seq(IntegerType(), IntegerType(), IntegerType())) == IntegerType())
    assert(leastUpperBound(Box(IntegerType()), Box(BooleanType())) == Untyped)
    assert(leastUpperBound(SetType(IntegerType()), SetType(IntegerType())) == SetType(IntegerType()))
    assert(leastUpperBound(BagType(IntegerType()), BagType(BooleanType())) == Untyped)
  }

  test("Bounds of refinement types") {
    val p = positive("p")
    assert(leastUpperBound(p, IntegerType()) == IntegerType())
    assert(leastUpperBound(IntegerType(), p) == IntegerType())
    assert(greatestLowerBound(p, IntegerType()) == p)
    assert(greatestLowerBound(IntegerType(), p) == p)

    // the predicate of the second refinement must be expressed over the binder of the first
    val e = even("e")
    for ((lower, join) <- Seq(true -> ((a: Expr, b: Expr) => And(a, b)), false -> ((a: Expr, b: Expr) => Or(a, b)))) {
      val bound = if (lower) greatestLowerBound(p, e) else leastUpperBound(p, e)
      val RefinementType(vd, pred) = bound: @unchecked
      assert(vd.getType == IntegerType())
      assert(exprOps.variablesOf(pred) == Set(vd.toVariable), s"free variables in $bound")
      assert(pred == join(p.prop, exprOps.replaceFromSymbols(Map(e.vd -> vd.toVariable), e.prop)))
    }
  }

  test("Bounds are contravariant in function and map domains") {
    val p = positive("p")
    assert(leastUpperBound(FunctionType(Seq(p), IntegerType()), FunctionType(Seq(IntegerType()), p)) ==
      FunctionType(Seq(p), IntegerType()))
    assert(greatestLowerBound(MapType(p, IntegerType()), MapType(IntegerType(), p)) ==
      MapType(IntegerType(), p))
    assert(leastUpperBound(FunctionType(Seq(IntegerType()), IntegerType()), FunctionType(Seq(), IntegerType())) == Untyped)
  }

  test("isSubtypeOf ignores refinements") {
    assert(isSubtypeOf(positive("p"), IntegerType()))
    assert(isSubtypeOf(IntegerType(), positive("p")))
    assert(isSubtypeOf(Untyped, BooleanType()))
    assert(!isSubtypeOf(IntegerType(), BooleanType()))
    typeCheck(E(BigInt(1)), BooleanType(), IntegerType())
    intercept[TypeErrorException](typeCheck(E(BigInt(1)), BooleanType()))
  }

  test("instantiation") {
    assert(instantiation(T, IntegerType()) == Some(Map(T -> IntegerType())))
    assert(instantiation(Box(T), Box(IntegerType())) == Some(Map(T -> IntegerType())))
    assert(instantiation(TupleType(Seq(T, U, T)), TupleType(Seq(IntegerType(), BooleanType(), IntegerType()))) ==
      Some(Map(T -> IntegerType(), U -> BooleanType())))
    assert(instantiation(TupleType(Seq(T, T)), TupleType(Seq(IntegerType(), BooleanType()))) == None)
    assert(instantiation(MapType(T, U), MapType(IntegerType(), Box(BooleanType()))) ==
      Some(Map(T -> IntegerType(), U -> Box(BooleanType()))))
    assert(instantiation(Box(T), IntegerType()) == None)
    assert(instantiation(T, Untyped) == None)
    assert(instantiation(ADTType(FreshIdentifier("Unknown"), Seq()), IntegerType()) == None)
  }

  test("typeCardinality") {
    assert(typeCardinality(UnitType()) == Some(1))
    assert(typeCardinality(Box(BooleanType())) == Some(2))
    assert(typeCardinality(Box(IntegerType())) == None)
    assert(typeCardinality(FunctionType(Seq(BooleanType()), Untyped)) == Some(0))
    assert(typeCardinality(BagType(Untyped)) == Some(1))
    // cardinalities that don't fit in an Int are unknown
    val big = TupleType(Seq.fill(40)(BooleanType()))
    assert(typeCardinality(big) == None)
    assert(typeCardinality(SetType(TupleType(Seq.fill(5)(BooleanType())))) == None)
    assert(typeCardinality(MapType(TupleType(Seq.fill(6)(BooleanType())), BooleanType())) == None)
  }

  test("typeDependencies") {
    val deps = typeDependencies(TupleType(Seq(Box(IntegerType()), SetType(BooleanType()))))
    assert(deps(TupleType(Seq(Box(IntegerType()), SetType(BooleanType())))) == Set(Box(IntegerType()), SetType(BooleanType())))
    assert(deps(Box(IntegerType())) == Set(IntegerType()))
    assert(deps(SetType(BooleanType())) == Set(BooleanType()))
    assert(deps(IntegerType()) == Set())
  }
}
