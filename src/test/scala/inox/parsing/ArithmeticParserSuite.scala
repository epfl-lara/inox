package inox
package parsing

import org.scalatest.funsuite.AnyFunSuite

class ArithmeticParserSuite extends AnyFunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing additions.") {

    assertResult(Plus(IntegerLiteral(3), IntegerLiteral(4))) {
      e"3 + 4"
    }

    assertResult(Plus(Plus(IntegerLiteral(3), IntegerLiteral(4)), IntegerLiteral(5))) {
      e"3 + 4 + 5"
    }
  }

  test("Parsing substractions.") {

    assertResult(Minus(IntegerLiteral(3), IntegerLiteral(4))) {
      e"3 - 4"
    }

    assertResult(Minus(Minus(IntegerLiteral(3), IntegerLiteral(4)), IntegerLiteral(5))) {
      e"3 - 4 - 5"
    }
  }

  test("Parsing multiplications.") {

    assertResult(Division(IntegerLiteral(3), IntegerLiteral(4))) {
      e"3 / 4"
    }

    assertResult(Division(Division(IntegerLiteral(3), IntegerLiteral(4)), IntegerLiteral(5))) {
      e"3 / 4 / 5"
    }
  }

  test("Parsing divisions.") {

    assertResult(Times(IntegerLiteral(3), IntegerLiteral(4))) {
      e"3 * 4"
    }

    assertResult(Times(Times(IntegerLiteral(3), IntegerLiteral(4)), IntegerLiteral(5))) {
      e"3 * 4 * 5"
    }
  }

  test("Parsing unary negation.") {
    assertResult(UMinus(IntegerLiteral(3))) {
      e"- 3"
    }

    assertResult(UMinus(IntegerLiteral(3))) {
      e"-(3)"
    }

    assertResult(UMinus(IntegerLiteral(-3))) {
      e"- -3"
    }

    assertResult(UMinus(IntegerLiteral(-3))) {
      e"-(-3)"
    }

    assertResult(UMinus(IntegerLiteral(-3))) {
      e"--3"
    }
  }

  test("Operator precedence.") {
    assertResult(Plus(IntegerLiteral(4), Times(IntegerLiteral(5), IntegerLiteral(6)))) {
      e"4 + 5 * 6"
    }
    
    assertResult(Plus(Times(IntegerLiteral(4), IntegerLiteral(5)), IntegerLiteral(6))) {
      e"4 * 5 + 6"
    }

    assertResult(Minus(Plus(Minus(IntegerLiteral(0), Division(IntegerLiteral(1), IntegerLiteral(2))), Times(Division(Times(UMinus(IntegerLiteral(3)), IntegerLiteral(4)), IntegerLiteral(5)), IntegerLiteral(6))), IntegerLiteral(7))) {
      e"0 - 1 / 2 + - 3 * 4 / 5 * 6 - 7"
    }
  }

  test("Parenthesized expressions.") {
    assertResult(IntegerLiteral(0)) {
      e"(0)"
    }

    assertResult(IntegerLiteral(42)) {
      e"((((42))))"
    }

    assertResult(Times(IntegerLiteral(1), Plus(IntegerLiteral(2), IntegerLiteral(3)))) {
      e"1 * (2 + 3)"
    }

    assertResult(UMinus(Times(IntegerLiteral(1), UMinus(Plus(IntegerLiteral(2), IntegerLiteral(3)))))) {
      e"-(1 * -(2 + ((3))))"
    }
  }
}