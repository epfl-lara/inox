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

    assertResult(BVType(32)) {
      t"Int32"
    }

    assertResult(BVType(64)) {
      t"Int64"
    }

    assertResult(BVType(17)) {
      t"Int17"
    }

    assertResult(BVType(1273)) {
      t"Int1273"
    }

    assertResult(BVType(1)) {
      t"Int1"
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
}
