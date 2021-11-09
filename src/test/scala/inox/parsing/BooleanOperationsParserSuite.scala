package inox
package parsing

import org.scalatest.funsuite.AnyFunSuite

class BooleanOperationsParserSuite extends AnyFunSuite {

  import inox.trees.{given, _}
  import interpolator.{given, _}
  given Symbols = NoSymbols

  test("Parsing conjunctions.") {

    assertResult(And(BooleanLiteral(true), BooleanLiteral(false))) {
      e"true && false"
    }

    assertResult(And(Seq(BooleanLiteral(true), BooleanLiteral(false), BooleanLiteral(true)))) {
      e"true && false && true"
    }

    assertResult(And(BooleanLiteral(true), And(BooleanLiteral(false), BooleanLiteral(true)))) {
      e"true && (false && true)"
    }

    assertResult(And(And(BooleanLiteral(true), BooleanLiteral(false)), BooleanLiteral(true))) {
      e"(true && false) && true"
    }
  }

  test("Parsing disjunctions.") {

    assertResult(Or(BooleanLiteral(true), BooleanLiteral(false))) {
      e"true || false"
    }

    assertResult(Or(Seq(BooleanLiteral(true), BooleanLiteral(false), BooleanLiteral(true)))) {
      e"true || false || true"
    }

    assertResult(Or(BooleanLiteral(true), Or(BooleanLiteral(false), BooleanLiteral(true)))) {
      e"true || (false || true)"
    }

    assertResult(Or(Or(BooleanLiteral(true), BooleanLiteral(false)), BooleanLiteral(true))) {
      e"(true || false) || true"
    }
  }

  test("Parsing implications.") {

    assertResult(Implies(BooleanLiteral(true), BooleanLiteral(false))) {
      e"true ==> false"
    }

    assertResult(Implies(BooleanLiteral(true), Implies(BooleanLiteral(false), BooleanLiteral(true)))) {
      e"true ==> false ==> true"
    }

    assertResult(Implies(BooleanLiteral(true), Implies(BooleanLiteral(false), BooleanLiteral(true)))) {
      e"true ==> (false ==> true)"
    }

    assertResult(Implies(Implies(BooleanLiteral(true), BooleanLiteral(false)), BooleanLiteral(true))) {
      e"(true ==> false) ==> true"
    }
  }

  test("Parsing negations.") {

    assertResult(Not(BooleanLiteral(false))) {
      e"!false"
    }

    assertResult(Not(Not(BooleanLiteral(true)))) {
      e"!!true"
    }
  }

  test("Operator precedence.") {

    assertResult(Implies(Or(Seq(Not(BooleanLiteral(false)), And(BooleanLiteral(false), Not(BooleanLiteral(true))), And(BooleanLiteral(true), BooleanLiteral(false)))), And(Not(BooleanLiteral(true)), BooleanLiteral(false)))) {
      e"!false || false && !true || true && false ==> !true && false"
    }
  }
}