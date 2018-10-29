package inox
package parser

import org.scalatest._

class ComparisonOperationsParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing equalities.") {

    assertResult(Equals(BooleanLiteral(true), BooleanLiteral(false))) {
      e"true == false"
    }

    assertResult(Equals(IntegerLiteral(1), IntegerLiteral(2))) {
      e"1 == 2"
    }

    assertResult(Equals(Int32Literal(1), Int32Literal(2))) {
      e"1 == 2 as Int"
    }

    assertResult(Equals(FractionLiteral(1, 1), FractionLiteral(2, 1))) {
      e"1 as Real == 2"
    }

    assertResult(Equals(FractionLiteral(3, 2), FractionLiteral(2, 1))) {
      e"1.5 == 2.0"
    }

    assertResult(Equals(StringLiteral("hello"), StringLiteral("world"))) {
      e"'hello' == 'world'"
    }

    assertResult(Equals(CharLiteral('A'), CharLiteral('B'))) {
      e"`A` == `B`"
    }

    assertResult(Equals(BVLiteral(true, 1, 17), BVLiteral(true, 4, 17))) {
      e"1 as Int17 == 4 as Int17"
    }
  }

  test("Parsing less-or-equals.") {

    assertThrows[InterpolatorException] {
      e"true <= false"
    }

    assertResult(LessEquals(IntegerLiteral(1), IntegerLiteral(2))) {
      e"1 <= 2"
    }

    assertResult(LessEquals(Int32Literal(1), Int32Literal(2))) {
      e"1 <= 2 as Int"
    }

    assertResult(LessEquals(FractionLiteral(1, 1), FractionLiteral(2, 1))) {
      e"1 as Real <= 2"
    }

    assertResult(LessEquals(FractionLiteral(3, 2), FractionLiteral(2, 1))) {
      e"1.5 <= 2.0"
    }

    assertThrows[InterpolatorException] {
      e"'hello' <= 'world'"
    }

    assertResult(LessEquals(CharLiteral('A'), CharLiteral('B'))) {
      e"`A` <= `B`"
    }

    assertResult(LessEquals(BVLiteral(true, 1, 17), BVLiteral(true, 4, 17))) {
      e"1 as Int17 <= 4 as Int17"
    }
  }

  test("Parsing greater-or-equals.") {

    assertThrows[InterpolatorException] {
      e"true >= false"
    }

    assertResult(GreaterEquals(IntegerLiteral(1), IntegerLiteral(2))) {
      e"1 >= 2"
    }

    assertResult(GreaterEquals(Int32Literal(1), Int32Literal(2))) {
      e"1 >= 2 as Int"
    }

    assertResult(GreaterEquals(FractionLiteral(1, 1), FractionLiteral(2, 1))) {
      e"1 as Real >= 2"
    }

    assertResult(GreaterEquals(FractionLiteral(3, 2), FractionLiteral(2, 1))) {
      e"1.5 >= 2.0"
    }

    assertThrows[InterpolatorException] {
      e"'hello' >= 'world'"
    }

    assertResult(GreaterEquals(CharLiteral('A'), CharLiteral('B'))) {
      e"`A` >= `B`"
    }

    assertResult(GreaterEquals(BVLiteral(true, 1, 17), BVLiteral(true, 4, 17))) {
      e"1 as Int17 >= 4 as Int17"
    }
  }

  test("Parsing less-than.") {

    assertThrows[InterpolatorException] {
      e"true < false"
    }

    assertResult(LessThan(IntegerLiteral(1), IntegerLiteral(2))) {
      e"1 < 2"
    }

    assertResult(LessThan(Int32Literal(1), Int32Literal(2))) {
      e"1 < 2 as Int"
    }

    assertResult(LessThan(FractionLiteral(1, 1), FractionLiteral(2, 1))) {
      e"1 as Real < 2"
    }

    assertResult(LessThan(FractionLiteral(3, 2), FractionLiteral(2, 1))) {
      e"1.5 < 2.0"
    }

    assertThrows[InterpolatorException] {
      e"'hello' < 'world'"
    }

    assertResult(LessThan(CharLiteral('A'), CharLiteral('B'))) {
      e"`A` < `B`"
    }

    assertResult(LessThan(BVLiteral(true, 1, 17), BVLiteral(true, 4, 17))) {
      e"1 as Int17 < 4 as Int17"
    }
  }

  test("Parsing greater-than.") {

    assertThrows[InterpolatorException] {
      e"true > false"
    }

    assertResult(GreaterThan(IntegerLiteral(1), IntegerLiteral(2))) {
      e"1 > 2"
    }

    assertResult(GreaterThan(Int32Literal(1), Int32Literal(2))) {
      e"1 > 2 as Int"
    }

    assertResult(GreaterThan(FractionLiteral(1, 1), FractionLiteral(2, 1))) {
      e"1 as Real > 2"
    }

    assertResult(GreaterThan(FractionLiteral(3, 2), FractionLiteral(2, 1))) {
      e"1.5 > 2.0"
    }

    assertThrows[InterpolatorException] {
      e"'hello' > 'world'"
    }

    assertResult(GreaterThan(CharLiteral('A'), CharLiteral('B'))) {
      e"`A` > `B`"
    }

    assertResult(GreaterThan(BVLiteral(true, 1, 17), BVLiteral(true, 4, 17))) {
      e"1 as Int17 > 4 as Int17"
    }
  }
}