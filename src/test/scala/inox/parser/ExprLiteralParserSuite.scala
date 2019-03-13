package inox
package parser

import scala.collection.BitSet
import org.scalatest._

class ExprLiteralParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing Boolean literals.") {

    assertResult(BooleanLiteral(true)) {
      e"true"
    }

    assertResult(BooleanLiteral(false)) {
      e"false"
    }
  }

  test("Parsing Char literals.") {

    assertResult(CharLiteral('A')) {
      e"`A`"
    }

    assertResult(CharLiteral('z')) {
      e"`z`"
    }

    assertResult(CharLiteral('7')) {
      e"`7`"
    }
  }

  test("Parsing Unit literal.") {

    assertResult(UnitLiteral()) {
      e"()"
    }
  }

  test("Parsing String literals.") {

    assertResult(StringLiteral("abc")) {
      e"'abc'"
    }

    assertResult(StringLiteral("")) {
      e"''"
    }
  }

  test("Parsing BigInt literals.") {

    assertResult(IntegerLiteral(0)) {
      e"0"
    }

    assertResult(IntegerLiteral(217)) {
      e"217"
    }

    assertResult(IntegerLiteral(-12)) {
      e"-12"
    }

    val large = "123456789012345678901234567890"

    assert(BigInt(BigInt(large).toInt) != BigInt(large))

    assertResult(IntegerLiteral(BigInt(large))) {
      e"123456789012345678901234567890"
    }
  }

  test("Parsing Int literals.") {

    assertResult(Int32Literal(0)) {
      e"0 as Int"
    }

    assertResult(Int32Literal(217)) {
      e"217 as Int"
    }

    assertResult(Int32Literal(-12)) {
      e"-12 as Int"
    }
  }

  test("Parsing BV literals.") {

    assertResult(BVLiteral(true, 0, 8)) {
      e"0 as Int8"
    }

    assertResult(BVLiteral(true, 7, 64)) {
      e"7 as Int64"
    }

    assertResult(BVLiteral(true, -1, 4)) {
      e"-1 as Int4"
    }

    assertResult(BVLiteral(true, BitSet(), 2)) {
      e"4 as Int2"
    }

    assertResult(BVLiteral(true, BitSet(1), 2)) {
      e"1 as Int2"
    }

    assertResult(BVLiteral(true, BitSet(2), 2)) {
      e"2 as Int2"
    }

    assertResult(BVLiteral(true, BitSet(1, 2), 2)) {
      e"3 as Int2"
    }

    assertResult(BVLiteral(true, BitSet(1, 2), 2)) {
      e"-1 as Int2"
    }
  }

  test("Parsing unsigned BV literals.") {

    assertResult(BVLiteral(false, 0, 8)) {
      e"0 as UInt8"
    }

    assertResult(BVLiteral(false, 2, 8)) {
      e"258 as UInt8"
    }

    assertResult(BVLiteral(false, 3, 5)) {
      e"1027 as UInt5"
    }

    assertResult(BVLiteral(false, 7, 64)) {
      e"7 as UInt64"
    }

    assertResult(BVLiteral(false, 15, 4)) {
      e"-1 as UInt4"
    }

    assertResult(BVLiteral(false, BitSet(), 2)) {
      e"4 as UInt2"
    }

    assertResult(BVLiteral(false, BitSet(1), 2)) {
      e"1 as UInt2"
    }

    assertResult(BVLiteral(false, BitSet(2), 2)) {
      e"2 as UInt2"
    }

    assertResult(BVLiteral(false, BitSet(1, 2), 2)) {
      e"3 as UInt2"
    }

    assertResult(BVLiteral(true, BitSet(1, 2), 2)) {
      e"-1 as Int2"
    }
  }

  test("Parsing Real literals.") {

    assertResult(FractionLiteral(0, 1)) {
      e"0.0"
    }

    assertResult(FractionLiteral(7, 1)) {
      e"7.0"
    }

    assertResult(FractionLiteral(7, 1)) {
      e"7 as Real"
    }

    assertResult(FractionLiteral(7, 2)) {
      e"3.5"
    }

    assertResult(FractionLiteral(21, 5)) {
      e"4.2"
    }

    assertResult(FractionLiteral(1, 3)) {
      e"0.(3)"
    }

    assertResult(FractionLiteral(1, 1)) {
      e"0.(9)"
    }

    assertResult(FractionLiteral(3227, 555)) {
      e"5.8(144)"
    }

    assertResult(FractionLiteral(-0, 1)) {
      e"-0.0"
    }

    assertResult(FractionLiteral(-7, 1)) {
      e"-7.0"
    }

    assertResult(FractionLiteral(-7, 1)) {
      e"-7 as Real"
    }

    assertResult(FractionLiteral(-7, 2)) {
      e"-3.5"
    }

    assertResult(FractionLiteral(-21, 5)) {
      e"-4.2"
    }

    assertResult(FractionLiteral(-1, 3)) {
      e"-0.(3)"
    }

    assertResult(FractionLiteral(-1, 1)) {
      e"-0.(9)"
    }

    assertResult(FractionLiteral(-3227, 555)) {
      e"-5.8(144)"
    }
  }
}