/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package transformers

import org.scalatest.funsuite.AnyFunSuite

import solvers.PurityOptions

/** The CNF path simplifier keeps path conditions in conjunctive normal form so
  * that it can discharge conditions that only follow from several clauses.
  */
class SimplifierWithCNFPathSuite extends AnyFunSuite with DatastructureUtils {
  import inox.trees.{given, _}
  import inox.trees.dsl._

  val symbols = baseSymbols
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

  val d = Variable.fresh("d", BooleanType())
  val e = Variable.fresh("e", BooleanType())

  test("Implications and conditionals on the path are split into clauses") {
    assert(simplify(IfExpr(b, i, j), Implies(a, b), a) == i)
    assert(simplify(IfExpr(b, i, j), IfExpr(a, b, c), a) == i)
    assert(simplify(IfExpr(c, i, j), IfExpr(a, b, c), Not(a)) == i)
  }

  test("Negations on the path are pushed into clauses") {
    assert(simplify(IfExpr(b, i, j), Not(And(a, b)), a) == j)
    assert(simplify(IfExpr(a, i, j), Not(Or(a, b))) == j)
    assert(simplify(IfExpr(b, i, j), Not(Implies(a, b))) == j)
    assert(simplify(IfExpr(a, i, j), Not(Not(a))) == i)
    assert(simplify(IfExpr(b, i, j), Not(IfExpr(a, b, c)), a) == j)
    assert(simplify(IfExpr(c, i, j), Not(IfExpr(a, b, c)), Not(a)) == j)
  }

  test("Large disjunctions are kept as a single clause") {
    // Distributing this disjunction would produce 16 clauses, among them `a || c || e || b`.
    val big = Or(Seq(And(a, b), And(c, d), And(e, a), And(b, c)))
    val s = simplifier
    val env = s.initEnv.withCond(big)
    assert(!env.implies(Or(Seq(a, c, e, b))))
    val small = Or(And(a, b), And(c, d))
    assert(s.initEnv.withCond(small).implies(Or(a, c)))
  }

  test("Clauses already on the path are shortened by new conditions") {
    // `a || b` becomes `b` once `!a` is known
    val s = simplifier
    val env = s.initEnv.withCond(Or(a, b)).withCond(Not(a))
    assert(env.implies(b))
    assert(s.transform(IfExpr(b, i, j), env) == i)
  }

  test("Conditions with lets are split under the let") {
    val y = "y" :: BooleanType()
    val cond = Let(y, a, And(y.toVariable, b))
    assert(simplify(IfExpr(b, i, j), cond) == i)
  }

  test("Large conditions and bindings are not tracked") {
    val large = (1 to 25).foldLeft(i: Expr)((acc, k) => Plus(acc, IntegerLiteral(k)))
    val s = simplifier
    val cond = Equals(large, j)
    val env = s.initEnv.withCond(cond)
    assert(!env.implies(cond))
    val y = "y" :: IntegerType()
    val bound = s.initEnv.withBinding(y -> large)
    assert(bound.expand(y.toVariable) == y.toVariable)
  }

  test("Integer bindings update the boolean bindings that use them") {
    val s = simplifier
    val p = "p" :: BooleanType()
    val y = "y" :: IntegerType()
    val env = s.initEnv.withBinding(p -> LessThan(i, j)).withBinding(y -> Plus(i, one)).withCond(p.toVariable)
    assert(s.transform(IfExpr(LessThan(i, j), one, two), env) == one)
  }

  test("Variables bound to constructors are expanded") {
    val s = simplifier
    val x = "x" :: T(optionID)(IntegerType())
    val y = "y" :: T(optionID)(IntegerType())
    val some = ADT(someID, Seq(IntegerType()), Seq(i))
    val env = s.initEnv.withBinding(x -> some).withBinding(y -> x.toVariable)
    assert(env.expand(x.toVariable) == some)
    assert(env.expand(y.toVariable) == some)
    assert(env.expand(i) == i)
    assert(env.implies(IsConstructor(x.toVariable, someID)))
    assert(s.transform(ADTSelector(x.toVariable, v), env) == i)
    assert(s.transform(IsConstructor(x.toVariable, noneID), env) == BooleanLiteral(false))
  }

  test("Lets used inside lambdas are checked for purity") {
    // With assumeChecked, purity under lambdas is checked by an unchecked simplifier,
    // which receives the current path.
    val y = "y" :: IntegerType()
    val z = "z" :: IntegerType()
    val e = Let(y, Division(i, j), Lambda(Seq(z), Plus(Plus(y.toVariable, y.toVariable), z.toVariable)))
    val res = simplify(e, a)
    assert(exprOps.variablesOf(res) == Set(i, j))
  }

  test("Paths can be moved to another CNF simplifier") {
    val s1 = simplifier
    val s2 = simplifier
    val env = s1.initEnv.withCond(And(a, b))
    assert(s2.transform(IfExpr(a, i, j), env `in` s2) == i)
  }

  test("Paths can be moved to the default simplifier") {
    val s = simplifier
    val y = "y" :: BooleanType()
    val env = s.initEnv.withBinding(y -> b).withCond(a)
    val default = symbols.simplifier(using PurityOptions.unchecked)
    val moved = env `in` default
    assert(default.transform(IfExpr(a, i, j), moved) == i)
    assert(moved.implies(a))
  }

  test("A path subsumes the paths that extend it") {
    val s = simplifier
    val y = "y" :: IntegerType()
    val base = s.initEnv.withCond(a).withBinding(y -> Plus(i, one))
    val extended = base.withCond(b)
    assert(base `subsumes` extended)
    assert(!(extended `subsumes` base))
    assert(s.initEnv `subsumes` base)
  }

  test("Paths print as the conjunction of their clauses") {
    val s = simplifier
    assert(s.initEnv.toString == "true")
    val str = s.initEnv.withCond(And(a, Or(b, c))).toString
    assert(str.contains("a") && str.contains("b || c") || str.contains("c || b"), str)
  }
}
