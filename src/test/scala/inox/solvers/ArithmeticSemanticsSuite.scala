/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Integer and real arithmetic on every solver. */
class ArithmeticSemanticsSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  given Symbols = symbols

  test("BigInt and Fraction Literals", Integers, Reals) { ctx =>
    val s = solver(ctx)
    check(s, IntegerLiteral(-1),     IntegerLiteral(-1))
    check(s, IntegerLiteral(0),      IntegerLiteral(0))
    check(s, IntegerLiteral(42),     IntegerLiteral(42))
    check(s, FractionLiteral(0, 1),  FractionLiteral(0, 1))
    check(s, FractionLiteral(42 ,1), FractionLiteral(42, 1))
    check(s, FractionLiteral(26, 3), FractionLiteral(26, 3))
  }

  test("Large Integer Literals", Integers) { ctx =>
    val s = solver(ctx)

    val twoTo32 = BigInt(2).pow(32)
    val twoTo100 = BigInt(2).pow(100)

    check(s, IntegerLiteral(twoTo32),         IntegerLiteral(twoTo32))
    check(s, IntegerLiteral(twoTo100 + 123), IntegerLiteral(twoTo100 + 123))
  }

  test("BigInt Arithmetic", Integers) { ctx =>
    val s = solver(ctx)

    check(s, Plus(IntegerLiteral(3), IntegerLiteral(5)),  IntegerLiteral(8))
    check(s, Minus(IntegerLiteral(7), IntegerLiteral(2)), IntegerLiteral(5))
    check(s, UMinus(IntegerLiteral(7)),                   IntegerLiteral(-7))
    check(s, Times(IntegerLiteral(2), IntegerLiteral(3)), IntegerLiteral(6))
  }

  test("BigInt Division, Modulo and Remainder", Integers) { ctx =>
    val s = solver(ctx)

    check(s, Division(IntegerLiteral(10), IntegerLiteral(3)),  IntegerLiteral(3))
    check(s, Remainder(IntegerLiteral(10), IntegerLiteral(3)), IntegerLiteral(1))
    check(s, Modulo(IntegerLiteral(10), IntegerLiteral(3)),    IntegerLiteral(1))

    check(s, Division(IntegerLiteral(-1), IntegerLiteral(3)),  IntegerLiteral(0))
    check(s, Remainder(IntegerLiteral(-1), IntegerLiteral(3)), IntegerLiteral(-1))
    check(s, Modulo(IntegerLiteral(-1), IntegerLiteral(3)),    IntegerLiteral(2))

    check(s, Division(IntegerLiteral(-1), IntegerLiteral(-3)), IntegerLiteral(0))
    check(s, Remainder(IntegerLiteral(-1), IntegerLiteral(-3)),IntegerLiteral(-1))
    check(s, Modulo(IntegerLiteral(-1), IntegerLiteral(-3)),   IntegerLiteral(2))

    check(s, Division(IntegerLiteral(1), IntegerLiteral(-3)),  IntegerLiteral(0))
    check(s, Remainder(IntegerLiteral(1), IntegerLiteral(-3)), IntegerLiteral(1))
    check(s, Modulo(IntegerLiteral(1), IntegerLiteral(-3)),    IntegerLiteral(1))
  }

  test("BigInt Comparisons", Integers) { ctx =>
    val s = solver(ctx)

    check(s, GreaterEquals(IntegerLiteral(7), IntegerLiteral(4)), BooleanLiteral(true))
    check(s, GreaterEquals(IntegerLiteral(7), IntegerLiteral(7)), BooleanLiteral(true))
    check(s, GreaterEquals(IntegerLiteral(4), IntegerLiteral(7)), BooleanLiteral(false))

    check(s, GreaterThan(IntegerLiteral(7), IntegerLiteral(4)),   BooleanLiteral(true))
    check(s, GreaterThan(IntegerLiteral(7), IntegerLiteral(7)),   BooleanLiteral(false))
    check(s, GreaterThan(IntegerLiteral(4), IntegerLiteral(7)),   BooleanLiteral(false))

    check(s, LessEquals(IntegerLiteral(7), IntegerLiteral(4)),    BooleanLiteral(false))
    check(s, LessEquals(IntegerLiteral(7), IntegerLiteral(7)),    BooleanLiteral(true))
    check(s, LessEquals(IntegerLiteral(4), IntegerLiteral(7)),    BooleanLiteral(true))

    check(s, LessThan(IntegerLiteral(7), IntegerLiteral(4)),      BooleanLiteral(false))
    check(s, LessThan(IntegerLiteral(7), IntegerLiteral(7)),      BooleanLiteral(false))
    check(s, LessThan(IntegerLiteral(4), IntegerLiteral(7)),      BooleanLiteral(true))
  }

  test("Real Arithmetic", Reals) { ctx =>
    val s = solver(ctx)

    check(s, Plus(FractionLiteral(2, 3), FractionLiteral(1, 3)),  FractionLiteral(1, 1))
    check(s, Minus(FractionLiteral(1, 1), FractionLiteral(1, 4)), FractionLiteral(3, 4))
    check(s, UMinus(FractionLiteral(7, 1)),                       FractionLiteral(-7, 1))
    check(s, Times(FractionLiteral(2, 3), FractionLiteral(1, 3)), FractionLiteral(2, 9))
  }

  test("Real Comparisons", Reals) { ctx =>
    val s = solver(ctx)

    check(s, GreaterEquals(FractionLiteral(7, 1), FractionLiteral(4, 2)),   BooleanLiteral(true))
    check(s, GreaterEquals(FractionLiteral(7, 2), FractionLiteral(49, 13)), BooleanLiteral(false))

    check(s, GreaterThan(FractionLiteral(49, 13), FractionLiteral(7, 2)),   BooleanLiteral(true))
    check(s, GreaterThan(FractionLiteral(49, 14), FractionLiteral(7, 2)),   BooleanLiteral(false))
    check(s, GreaterThan(FractionLiteral(4, 2), FractionLiteral(7, 1)),     BooleanLiteral(false))

    check(s, LessEquals(FractionLiteral(7, 1), FractionLiteral(4, 2)),      BooleanLiteral(false))
    check(s, LessEquals(FractionLiteral(7, 2), FractionLiteral(49, 13)),    BooleanLiteral(true))

    check(s, LessThan(FractionLiteral(49, 13), FractionLiteral(7, 2)),      BooleanLiteral(false))
    check(s, LessThan(FractionLiteral(49, 14), FractionLiteral(7, 2)),      BooleanLiteral(false))
    check(s, LessThan(FractionLiteral(4, 2), FractionLiteral(7, 1)),        BooleanLiteral(true))
  }

  test("Real Equality and Division", Reals) { ctx =>
    val s = solver(ctx)

    check(s, Division(FractionLiteral(1, 2), FractionLiteral(-1, 3)), FractionLiteral(-3, 2))
    check(s, LessThan(Division(FractionLiteral(1, 2), FractionLiteral(-1, 3)), FractionLiteral(0, 1)), BooleanLiteral(true))
    check(s, Equals(Division(FractionLiteral(1, 1), FractionLiteral(2, 1)), Division(FractionLiteral(2, 1), FractionLiteral(4, 1))), BooleanLiteral(true))

    val x = Variable.fresh("x", RealType())
    s.solveSAT(Equals(Times(x, FractionLiteral(2, 1)), FractionLiteral(1, 1))) match {
      case SatWithModel(model) => assert(model.vars.get(x.toVal) == Some(FractionLiteral(1, 2)))
      case got => fail(s"Expected a model for x * 2 == 1 but got $got")
    }

    assert(s.solveVALID(Implies(Equals(x, FractionLiteral(-1, 1)), LessThan(x, FractionLiteral(0, 1)))) contains true)
    assert(s.solveVALID(Implies(
      LessThan(x, FractionLiteral(0, 1)),
      GreaterThan(Division(FractionLiteral(1, 1), x), FractionLiteral(-1000000, 1))
    )) contains false)

    // Division by zero is unspecified (as in SMT-LIB), but it is still a function of the dividend
    val zero = FractionLiteral(0, 1)
    assert(s.solveVALID(Equals(Division(FractionLiteral(1, 1), zero), Division(FractionLiteral(2, 1), zero))) contains false)
    assert(s.solveVALID(Equals(Division(FractionLiteral(1, 1), zero), zero)) contains false)
    assert(s.solveVALID(Equals(Division(x, zero), Division(x, zero))) contains true)
  }
}
