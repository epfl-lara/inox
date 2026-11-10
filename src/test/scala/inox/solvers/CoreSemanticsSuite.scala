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

  test("Char Literals and Comparisons") { ctx =>
    val s = solver(ctx)

    check(s, CharLiteral('a'), CharLiteral('a'))
    check(s, CharLiteral('\u00e9'), CharLiteral('\u00e9'))
    check(s, Equals(CharLiteral('a'), CharLiteral('a')), BooleanLiteral(true))
    check(s, Equals(CharLiteral('a'), CharLiteral('b')), BooleanLiteral(false))
    check(s, LessThan(CharLiteral('a'), CharLiteral('b')), BooleanLiteral(true))
    check(s, LessThan(CharLiteral('b'), CharLiteral('a')), BooleanLiteral(false))
    check(s, LessEquals(CharLiteral('a'), CharLiteral('a')), BooleanLiteral(true))
    check(s, LessEquals(CharLiteral('\u00e9'), CharLiteral('a')), BooleanLiteral(false))
    check(s, GreaterThan(CharLiteral('\u00e9'), CharLiteral('a')), BooleanLiteral(true))
    check(s, GreaterThan(CharLiteral('a'), CharLiteral('a')), BooleanLiteral(false))
    check(s, GreaterEquals(CharLiteral('b'), CharLiteral('a')), BooleanLiteral(true))
    check(s, GreaterEquals(CharLiteral('a'), CharLiteral('b')), BooleanLiteral(false))
  }

  test("Conditionals, Implications and Assumptions") { ctx =>
    val s = solver(ctx)

    val t = BooleanLiteral(true)
    val f = BooleanLiteral(false)
    check(s, IfExpr(t, Int32Literal(1), Int32Literal(2)), Int32Literal(1))
    check(s, IfExpr(f, Int32Literal(1), Int32Literal(2)), Int32Literal(2))
    check(s, IfExpr(f, t, f), f)
    check(s, IfExpr(t, t, f), t)
    check(s, Not(IfExpr(Equals(Int32Literal(1), Int32Literal(2)), t, f)), t)
    check(s, Implies(t, f), f)
    check(s, Implies(f, f), t)
    check(s, Equals(t, Not(f)), t)
    check(s, Assume(t, Int32Literal(3)), Int32Literal(3))
    check(s, Assume(GreaterThan(Int32Literal(3), Int32Literal(2)), t), t)
  }

  test("Lets of every type") { ctx =>
    val s = solver(ctx)

    val b = Variable.fresh("b", BooleanType())
    check(s, Let(b.toVal, BooleanLiteral(true), And(b, Not(Not(b)))), BooleanLiteral(true))
    check(s, Let(b.toVal, BooleanLiteral(false), IfExpr(b, Int32Literal(1), Int32Literal(2))), Int32Literal(2))
    val c = Variable.fresh("c", CharType())
    check(s, Let(c.toVal, CharLiteral('x'), Equals(c, CharLiteral('x'))), BooleanLiteral(true))
    val u = Variable.fresh("u", UnitType())
    check(s, Let(u.toVal, UnitLiteral(), u), UnitLiteral())
    val i = Variable.fresh("i", Int32Type())
    check(s, Let(i.toVal, Int32Literal(2), LessThan(i, Int32Literal(3))), BooleanLiteral(true))
  }
}
