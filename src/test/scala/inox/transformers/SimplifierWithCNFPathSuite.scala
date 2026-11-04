/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

import org.scalatest.funsuite.AnyFunSuite

import solvers.PurityOptions

/** The CNF path simplifier keeps path conditions in conjunctive normal form so
  * that it can discharge conditions that only follow from several clauses.
  */
class SimplifierWithCNFPathSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl._

  val symbols = NoSymbols
  given Symbols = symbols

  class CNFSimplifier(override val trees: inox.trees.type,
                      override val symbols: SimplifierWithCNFPathSuite.this.symbols.type,
                      override val s: inox.trees.type,
                      override val t: inox.trees.type,
                      override val opts: PurityOptions)
    extends SimplifierWithPC with SimplifierWithCNFPath

  def simplifier = new CNFSimplifier(inox.trees, symbols, inox.trees, inox.trees, PurityOptions.assumeChecked)

  val a = Variable.fresh("a", BooleanType())
  val b = Variable.fresh("b", BooleanType())
  val c = Variable.fresh("c", BooleanType())
  val i = Variable.fresh("i", IntegerType())
  val j = Variable.fresh("j", IntegerType())
  val one = IntegerLiteral(1)
  val two = IntegerLiteral(2)

  def simplify(e: Expr, conds: Expr*): Expr = {
    val s = simplifier
    s.transform(e, s.initEnv.withConds(conds))
  }

  test("Expressions without conditions simplify like the default simplifier") {
    for (e <- Seq(
      And(a, BooleanLiteral(true)),
      Or(Seq(a, BooleanLiteral(false), b)),
      Not(Not(a)),
      IfExpr(BooleanLiteral(true), i, j),
      Plus(i, IntegerLiteral(0)),
      Let("x" :: IntegerType(), one, Plus(i, one))
    )) {
      assert(simplify(e) == symbols.simplifyExpr(e)(using PurityOptions.assumeChecked), e)
    }
  }

  test("A condition on the path decides a branch") {
    assert(simplify(IfExpr(a, i, j), a) == i)
    assert(simplify(IfExpr(a, i, j), Not(a)) == j)
    assert(simplify(IfExpr(a, i, j)) == IfExpr(a, i, j))
  }

  test("A disjunction follows from its clauses in any order") {
    assert(simplify(IfExpr(Or(b, a), i, j), Or(a, b)) == i)
  }

  test("Conjunctions on the path are split into clauses") {
    assert(simplify(IfExpr(b, i, j), And(a, b)) == i)
    assert(simplify(And(Seq(a, b, c)), And(a, b)) == c)
  }

  test("Resolution between clauses decides a branch") {
    // a ==> b and a together imply b
    assert(simplify(IfExpr(b, i, j), Implies(a, b), a) == i)
    // a || b and !a imply b
    assert(simplify(IfExpr(b, i, j), Or(a, b), Not(a)) == i)
  }

  test("The path implies its clauses") {
    val s = simplifier
    val env = s.initEnv.withCond(And(a, Or(b, c)))
    assert(env.implies(a))
    assert(env.implies(Or(c, b)))
    assert(!env.implies(b))
  }

  test("Negating a path negates its conditions") {
    val s = simplifier
    val env = s.initEnv.withCond(a).negate
    assert(s.transform(IfExpr(a, i, j), env) == j)
  }

  test("Merging paths keeps the conditions of both") {
    val s = simplifier
    val env = s.initEnv.withCond(a) `merge` s.initEnv.withCond(b)
    assert(s.transform(And(a, b), env) == BooleanLiteral(true))
  }

  test("Boolean bindings are used to decide conditions") {
    val s = simplifier
    val y = "y" :: BooleanType()
    val env = s.initEnv.withBinding(y -> And(a, b)).withCond(y.toVariable)
    assert(s.transform(IfExpr(a, i, j), env) == i)
  }

  test("Let bindings are tracked in the path") {
    val e = Let("y" :: BooleanType(), a, IfExpr(a, IfExpr(a, i, j), j))
    assert(simplify(e) == IfExpr(a, i, j))
  }

  test("A let simplified under a condition is not reused without it") {
    val s = simplifier
    val y = "y" :: IntegerType()
    val e = Let(y, Plus(i, one), IfExpr(a, y.toVariable, Plus(y.toVariable, j)))
    // Under `a`, the let only keeps its then-branch...
    assert(s.transform(e, s.initEnv.withCond(a)) == Plus(i, one))
    // ...which must not be the result once `a` is no longer known.
    assert(s.transform(e, s.initEnv) == symbols.simplifyExpr(e)(using PurityOptions.assumeChecked))
    // Under `!a`, the result simplified without conditions may be reused, which is sound.
    assert(s.transform(e, s.initEnv.withCond(Not(a))) != Plus(i, one))
    val fresh = simplifier
    assert(fresh.transform(e, fresh.initEnv.withCond(Not(a))) == Plus(Plus(i, one), j))
  }

  test("A let simplified without conditions is reused under more conditions") {
    val s = simplifier
    val y = "y" :: IntegerType()
    val e = Let(y, Plus(i, one), IfExpr(Equals(y.toVariable, j), y.toVariable, j))
    val unconditional = s.transform(e, s.initEnv)
    assert(s.transform(e, s.initEnv.withCond(b)) == unconditional)
  }

  test("Cached lets are renamed to the variables of the current path") {
    val s = simplifier
    val y = "y" :: IntegerType()
    val u = "u" :: IntegerType()
    val w = "w" :: IntegerType()
    def let(v: ValDef) = Let(y, Plus(v.toVariable, one), IfExpr(Equals(y.toVariable, j), y.toVariable, j))
    // `u` and `w` have the same definition, so both lets normalize to the same expression
    val withU = s.transform(let(u), s.initEnv.withBinding(u -> Plus(i, one)))
    val withW = s.transform(let(w), s.initEnv.withBinding(w -> Plus(i, one)))
    assert(exprOps.variablesOf(withU) contains u.toVariable)
    assert(exprOps.variablesOf(withW) contains w.toVariable)
    assert(!(exprOps.variablesOf(withW) contains u.toVariable))
  }

  test("Integer conditions are kept as atoms") {
    val cond = LessThan(i, j)
    assert(simplify(IfExpr(LessThan(i, j), one, two), cond) == one)
    assert(simplify(IfExpr(Not(LessThan(i, j)), one, two), cond) == two)
  }
}
