package inox
package parsing

import org.scalatest.funsuite.AnyFunSuite

class OperationsPrecedenceParserSuite extends AnyFunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing a mix of boolean, comparison and arithmetic operations.") {

    assertResult {
      Implies(
        Or(
          Equals(
            Plus(
              IntegerLiteral(1), 
              Times(
                IntegerLiteral(2),
                IntegerLiteral(3))),
            IntegerLiteral(4)),
          And(
            Equals(
              LessEquals(
                IntegerLiteral(3),
                IntegerLiteral(2)),
              GreaterThan(
                IntegerLiteral(7),
                Plus(
                  IntegerLiteral(2),
                  IntegerLiteral(2)))),
            LessEquals(
              IntegerLiteral(18),
              IntegerLiteral(2)))),
        LessEquals(
          Times(
            IntegerLiteral(12),
            IntegerLiteral(8)),
          IntegerLiteral(2)))
    }{
      e"1 + 2 * 3 == 4 || 3 <= 2 == 7 > 2 + 2 && 18 <= 2 ==> 12 * 8 <= 2"
    }
  }
}