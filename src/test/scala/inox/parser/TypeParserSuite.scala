package inox
package parser

import org.scalatest._

class TypeParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing basic types") {

    assertResult(IntegerType()) {
      t"Integer"
    }

    assertResult(BooleanType()) {
      t"Boolean"
    }

    assertResult(UnitType()) {
      t"Unit"
    }

    assertResult(CharType()) {
      t"Char"
    }

    assertResult(StringType()) {
      t"String"
    }

    assertResult(Int32Type()) {
      t"Int"
    }

    assertResult(RealType()) {
      t"Real"
    }
  }

  test("Parsing with parentheses") {

    assertResult(IntegerType()) {
      t"(Integer)"
    }

    assertResult(BooleanType()) {
      t"((Boolean))"
    }

    assertResult(UnitType()) {
      t"(((Unit)))"
    }
  }

  test("Parsing BitVector types") {

    assertResult(BVType(true, 32)) {
      t"Int32"
    }

    assertResult(BVType(true, 64)) {
      t"Int64"
    }

    assertResult(BVType(true, 17)) {
      t"Int17"
    }

    assertResult(BVType(true, 1273)) {
      t"Int1273"
    }

    assertResult(BVType(true, 1)) {
      t"Int1"
    }
  }

  test("Parsing unsigned BitVector types") {

    assertResult(BVType(false, 32)) {
      t"UInt32"
    }

    assertResult(BVType(false, 64)) {
      t"UInt64"
    }

    assertResult(BVType(false, 17)) {
      t"UInt17"
    }

    assertResult(BVType(false, 1273)) {
      t"UInt1273"
    }

    assertResult(BVType(false, 1)) {
      t"UInt1"
    }
  }

  test("Parsing Set types") {

    assertResult(SetType(IntegerType())) {
      t"Set[Integer]"
    }

    assertResult(SetType(BooleanType())) {
      t"Set[Boolean]"
    }
  }

  test("Parsing Bag types") {

    assertResult(BagType(IntegerType())) {
      t"Bag[Integer]"
    }

    assertResult(BagType(BooleanType())) {
      t"Bag[Boolean]"
    }
  }

  test("Parsing Map types") {

    assertResult(MapType(StringType(), IntegerType())) {
      t"Map[String, Integer]"
    }

    assertResult(MapType(UnitType(), BooleanType())) {
      t"Map[Unit, Boolean]"
    }
  }

  test("Parsing Tuple types") {

    assertResult(TupleType(Seq(StringType(), IntegerType(), CharType()))) {
      t"(String, Integer, Char)"
    }

    assertResult(TupleType(Seq(UnitType(), BooleanType()))) {
      t"(Unit, Boolean)"
    }
  }

  test("Parsing Function types") {

    assertResult(FunctionType(Seq(IntegerType()), StringType())) {
      t"Integer => String"
    }

    assertResult(FunctionType(Seq(), StringType())) {
      t"() => String"
    }

    assertResult(FunctionType(Seq(IntegerType()), StringType())) {
      t"(Integer) => String"
    }

    assertResult(FunctionType(Seq(StringType(), IntegerType(), CharType()), BooleanType())) {
      t"(String, Integer, Char) => Boolean"
    }

    assertResult(FunctionType(Seq(TupleType(Seq(StringType(), IntegerType(), CharType()))), BooleanType())) {
      t"((String, Integer, Char)) => Boolean"
    }

    assertResult(FunctionType(Seq(IntegerType()), FunctionType(Seq(UnitType()), BooleanType()))) {
      t"Integer => Unit => Boolean"
    }
  }

  test("Parsing refinement types") {
    val t = t"{ w: String | length(w) >= 10 }"

    assert(t.isInstanceOf[RefinementType])

    val r = t.asInstanceOf[RefinementType]

    assert(r.vd.tpe == StringType())
    assert(r.vd.id.name == "w")

    assert(r.prop == GreaterEquals(StringLength(r.vd.toVariable), IntegerLiteral(10)))
  }

  test("Parsing Pi types") {

    val t = t"Pi (x: Int) => { y: Int | x > y }"

    assert(t.isInstanceOf[PiType])

    val p = t.asInstanceOf[PiType]

    assert(p.params.size == 1)
    assert(p.params(0).tpe == Int32Type())
    assert(p.params(0).id.name == "x")
    assert(p.to.isInstanceOf[RefinementType])

    val r = p.to.asInstanceOf[RefinementType]

    assert(r.vd.tpe == Int32Type())
    assert(r.vd.id.name == "y")

    assert(r.prop == GreaterThan(p.params(0).toVariable, r.vd.toVariable))
  }

  test("Parsing Pi types with multiple params") {

    val t = t"Pi (x: Integer, y: Integer, s: String) => { z: Integer | z + length(s) < x + y  }"

    assert(t.isInstanceOf[PiType])

    val p = t.asInstanceOf[PiType]

    assert(p.params.size == 3)
    assert(p.params(0).tpe == IntegerType())
    assert(p.params(1).tpe == IntegerType())
    assert(p.params(2).tpe == StringType())
    assert(p.params(0).id.name == "x")
    assert(p.params(1).id.name == "y")
    assert(p.params(2).id.name == "s")
  }

  test("Parsing Sigma types") {

    val t = t"Sigma (x: Int) => { y: Int | x > y }"

    assert(t.isInstanceOf[SigmaType])

    val s = t.asInstanceOf[SigmaType]

    assert(s.params.size == 1)
    assert(s.params(0).tpe == Int32Type())
    assert(s.params(0).id.name == "x")
    assert(s.to.isInstanceOf[RefinementType])

    val r = s.to.asInstanceOf[RefinementType]

    assert(r.vd.tpe == Int32Type())
    assert(r.vd.id.name == "y")

    assert(r.prop == GreaterThan(s.params(0).toVariable, r.vd.toVariable))
  }

  test("Parsing Sigma types with multiple params") {

    val t = t"Sigma (x: Integer, y: Integer, s: String) => { z: Integer | z + length(s) < x + y  }"

    assert(t.isInstanceOf[SigmaType])

    val p = t.asInstanceOf[SigmaType]

    assert(p.params.size == 3)
    assert(p.params(0).tpe == IntegerType())
    assert(p.params(1).tpe == IntegerType())
    assert(p.params(2).tpe == StringType())
    assert(p.params(0).id.name == "x")
    assert(p.params(1).id.name == "y")
    assert(p.params(2).id.name == "s")
  }

  test("Parsing complex type") {

    val t = t"Sigma (x: Int, y: Int) => (Pi (x: Int, z: Int) => String) => { z: Int | x + y == z }"

    t match {
      case SigmaType(p1s, FunctionType(Seq(PiType(p2s, StringType())), RefinementType(vd, Equals(Plus(x, y), z)))) => {
        assert(p1s.size == 2)
        assert(p1s(0).tpe == Int32Type())
        assert(p1s(1).tpe == Int32Type())
        assert(p1s(0).id.name == "x")
        assert(p1s(1).id.name == "y")

        assert(p2s.size == 2)
        assert(p2s(0).tpe == Int32Type())
        assert(p2s(1).tpe == Int32Type())
        assert(p2s(0).id.name == "x")
        assert(p2s(1).id.name == "z")

        assert(p1s(0).id != p2s(0).id)

        assert(vd.tpe == Int32Type())
        assert(vd.id.name == "z")

        assert(vd.id != p2s(1).id)

        assert(x == p1s(0).toVariable)
        assert(y == p1s(1).toVariable)
        assert(z == vd.toVariable)
      }
      case _ => fail("No match.")
    }

  }
}
