/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Booleans, lets and machine integer literals on every solver. */
class CoreSemanticsSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  given Symbols = symbols

  test("Boolean, Int and Unit Literals") { ctx =>
    val s = solver(ctx)

    check(s, BooleanLiteral(true),   BooleanLiteral(true))
    check(s, BooleanLiteral(false),  BooleanLiteral(false))
    check(s, Int8Literal(-1),        Int8Literal(-1))
    check(s, Int8Literal(0),         Int8Literal(0))
    check(s, Int8Literal(58),        Int8Literal(58))
    check(s, Int16Literal(58),       Int16Literal(58))
    check(s, Int16Literal(-1),       Int16Literal(-1))
    check(s, Int16Literal(0),        Int16Literal(0))
    check(s, Int32Literal(-1),       Int32Literal(-1))
    check(s, Int32Literal(0),        Int32Literal(0))
    check(s, Int32Literal(42),       Int32Literal(42))
    check(s, UnitLiteral(),          UnitLiteral())
  }

  test("Boolean Operations") { ctx =>
    val s = solver(ctx)

    check(s, And(BooleanLiteral(true), BooleanLiteral(true)),   BooleanLiteral(true))
    check(s, And(BooleanLiteral(true), BooleanLiteral(false)),  BooleanLiteral(false))
    check(s, And(BooleanLiteral(false), BooleanLiteral(false)), BooleanLiteral(false))
    check(s, And(BooleanLiteral(false), BooleanLiteral(true)),  BooleanLiteral(false))
    check(s, Or(BooleanLiteral(true), BooleanLiteral(true)),    BooleanLiteral(true))
    check(s, Or(BooleanLiteral(true), BooleanLiteral(false)),   BooleanLiteral(true))
    check(s, Or(BooleanLiteral(false), BooleanLiteral(false)),  BooleanLiteral(false))
    check(s, Or(BooleanLiteral(false), BooleanLiteral(true)),   BooleanLiteral(true))
    check(s, Not(BooleanLiteral(false)),                        BooleanLiteral(true))
    check(s, Not(BooleanLiteral(true)),                         BooleanLiteral(false))
  }

  test("Let") { ctx =>
    val s = solver(ctx)

    val v = Variable.fresh("id", Int32Type())
    check(s, Let(v.toVal, Int32Literal(42), v), Int32Literal(42))
    check(s, Let(v.toVal, Int32Literal(42), Plus(v, Int32Literal(1))), Int32Literal(43))
  }
}
