/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package smtlib3

import org.scalatest.funsuite.AnyFunSuite

import java.io.StringReader

class ParserSuite extends AnyFunSuite {
  import inox.trees._
  import solvers._

  given ctx: Context = TestContext(Options(Seq(
    optSelectedSolvers(Set("nativez3")),
    optCheckModels(true),
    optTimeout(10),
  )))

  private def parse(script: String): Seq[(InoxProgram, Expr)] =
    Parser(new StringReader(script)).parseScript

  private def parseOne(script: String): (InoxProgram, Expr) = {
    val problems = parse(script)
    assert(problems.size == 1, s"expected one check-sat, found ${problems.size}")
    problems.head
  }

  private def solve(script: String): String = {
    val (program, expr) = parseOne(script)
    import program.symbols.given
    assert(expr.isTyped, s"ill-typed assertion: $expr")
    for (fd <- program.symbols.functions.values) {
      assert(fd.fullBody.isTyped, s"ill-typed function: $fd")
    }
    val res = SimpleSolverAPI(program.getSolver).solveSAT(expr)
    if (res.isSAT) "sat" else if (res.isUNSAT) "unsat" else "unknown"
  }

  private def assertSAT(script: String): Unit = assert(solve(script) == "sat")
  private def assertUNSAT(script: String): Unit = assert(solve(script) == "unsat")

  /** The type of the free variable named `name` in the assertion of `script`. */
  private def typeOf(script: String, name: String): Type = {
    val (_, expr) = parseOne(script + "\n(check-sat)")
    exprOps.variablesOf(expr).find(_.id.name == name).getOrElse(fail(s"no variable $name in $expr")).tpe
  }

  test("SMT-LIB 2 scripts") {
    assertUNSAT(
      """(set-logic ALL)
        |(set-info :status unsat)
        |(declare-fun f (Int) Int)
        |(define-fun double ((x Int)) Int (+ x x))
        |(assert (= (f 1) (double 2)))
        |(assert (not (= (f 1) 4)))
        |(check-sat)
        |(exit)""".stripMargin)
  }

  test("function types") {
    val script =
      """(declare-const f (-> Int Bool Int))
        |(assert (= (f 1 true) 2))""".stripMargin
    assert(typeOf(script, "f") == FunctionType(Seq(IntegerType(), BooleanType()), IntegerType()))
    assertSAT(script + "\n(check-sat)")
  }

  test("unicode arrows") {
    val script =
      """(declare-const f (→ Int Int))
        |(assert (= (f 1) 2))""".stripMargin
    assert(typeOf(script, "f") == FunctionType(Seq(IntegerType()), IntegerType()))
  }

  test("dependent function types") {
    val decl =
      """(declare-const isqrt (-> (! Int :var n :restrict (>= n 0))
        |                         (! Int :var r :restrict (and (>= r 0) (<= (* r r) n) (< n (* (+ r 1) (+ r 1)))))))
        |""".stripMargin

    typeOf(decl + "(assert (= (isqrt 4) 2))", "isqrt") match {
      case PiType(Seq(ValDef(_, RefinementType(_, _), _)), RefinementType(_, pred)) =>
        assert(exprOps.variablesOf(pred).exists(_.id.name == "n"), s"codomain doesn't depend on n: $pred")
      case tpe => fail(s"unexpected type $tpe")
    }

    assertUNSAT(decl + "(assert (= (isqrt 4) 3))\n(check-sat)")
    // the codomain only holds in the domain
    assertSAT(decl + "(assert (= (isqrt (- 1)) 42))\n(check-sat)")
  }

  test("predicate subtypes") {
    val script = "(declare-const x (! Int :var x :restrict (> x 0)))\n(assert (< x 1))"
    assert(typeOf(script, "x").isInstanceOf[RefinementType])
    assertUNSAT(script + "\n(check-sat)")
  }

  test("polymorphism through type variables") {
    assertUNSAT(
      """(declare-type-var X)
        |(define-fun id ((x X)) X x)
        |(assert (or (not (= (id 1) 1)) (id false)))
        |(check-sat)""".stripMargin)

    assertUNSAT(
      """(declare-type-var A)
        |(declare-type-var B)
        |(define-fun app ((f (-> A B)) (x A)) B (f x))
        |(assert (not (= (app (lambda ((x Int)) (+ x 1)) 1) 2)))
        |(check-sat)""".stripMargin)

    // declared polymorphic constants are functions without body, used at several types
    assertSAT(
      """(declare-type-var A)
        |(declare-const pick (-> A A A))
        |(declare-const empty A)
        |(assert (and (= (pick 1 2) 3) (pick true false) (= (as empty Int) 0) (as empty Bool)))
        |(check-sat)""".stripMargin)
  }

  test("type definitions") {
    assertUNSAT(
      """(define-type AtLeast ((! Int :var n)) (! Int :var x :restrict (>= x n)))
        |(declare-const y (AtLeast 5))
        |(assert (< y 3))
        |(check-sat)""".stripMargin)

    val script =
      """(define-type Map (K V) (Array K V))
        |(define-sort Set2 (E) (Map E Bool))
        |(declare-const m (Set2 Int))
        |(assert (select m 1))""".stripMargin
    assert(typeOf(script, "m") == MapType(IntegerType(), BooleanType()))
  }

  test("declared types") {
    assertSAT(
      """(declare-type U ())
        |(declare-type Pair (Type Type))
        |(declare-const a U)
        |(declare-const b U)
        |(declare-const p (Pair U Int))
        |(assert (not (= a b)))
        |(check-sat)""".stripMargin)

    intercept[tip.MissformedTIPException] {
      parse("(declare-type BV (Int))\n(check-sat)")
    }
  }

  test("constant definitions") {
    assertUNSAT(
      """(define-const two Int 2)
        |(define-const inc (-> Int Int) (lambda ((x Int)) (+ x 1)))
        |(define-const-rec fact (-> Int Int)
        |  (lambda ((n Int)) (ite (<= n 0) 1 (* n (fact (- n 1))))))
        |(assert (or (not (= (inc two) 3)) (not (= (fact 3) 6))))
        |(check-sat)""".stripMargin)
  }

  test("partial and curried applications") {
    assertUNSAT(
      """(define-fun add ((x Int) (y Int)) Int (+ x y))
        |(define-const add1 (-> Int Int) (add 1))
        |(define-fun mk ((x Int)) (-> Int Int) (lambda ((y Int)) (+ x y)))
        |(declare-const g (-> Int Int Int))
        |(assert (or (not (= (add1 2) 3)) (not (= (mk 1 2) 3)) (not (= (@ (add 1) 2) 3))))
        |(check-sat)""".stripMargin)
    assertSAT(
      """(declare-const g (-> Int Int Int))
        |(assert (= (@ (g 1) 2) 3))
        |(check-sat)""".stripMargin)
  }

  test("higher-order binders") {
    assertUNSAT(
      """(declare-const p (-> Int Bool))
        |(assert (exists p))
        |(assert (forall ((x Int)) (not (p x))))
        |(check-sat)""".stripMargin)

    assertUNSAT(
      """(assert (not (forall (lambda ((x Int)) (>= (* x x) 0)))))
        |(check-sat)""".stripMargin)

    assertUNSAT(
      """(assert (or (= (choose (x Int) (= x 3)) 4) (= (choose (lambda ((y Int)) (= y 3))) 5)))
        |(check-sat)""".stripMargin)
  }

  test("SMT-LIB 2.6 datatypes and matches") {
    val datatypes =
      """(declare-datatypes ((List 1)) ((par (E) ((nil) (cons (head E) (tail (List E)))))))
        |(declare-datatype Color ((red) (green) (blue)))
        |(define-fun-rec len ((l (List Int))) Int
        |  (match l ((nil 0) ((cons h t) (+ 1 (len t))))))
        |(define-fun warm ((c Color)) Bool (match c ((red true) (other false))))
        |""".stripMargin

    assertUNSAT(datatypes +
      """(assert (or (not (= (len (cons 1 (cons 2 (as nil (List Int))))) 2))
        |            (warm blue) (not (warm red))
        |            ((_ is nil) (cons 1 (as nil (List Int))))
        |            (not (is-cons (cons 1 (as nil (List Int)))))))
        |(check-sat)""".stripMargin)
  }

  test("TIP syntax") {
    assertUNSAT(
      """(declare-datatypes () ((Nat (Z) (S (p Nat)))))
        |(define-fun-rec plus ((x Nat) (y Nat)) Nat (match x (case Z y) (case (S n) (S (plus n y)))))
        |(datatype-invariant n Nat (not (= n (S (S (S Z))))))
        |(declare-const n Nat)
        |(assert (= n (plus (S Z) (S (S Z)))))
        |(check-sat)""".stripMargin)
  }

  test("bit-vectors") {
    val script = "(declare-const b (BitVec 8))\n(assert (= b #x0F))"
    assert(typeOf(script, "b") == BVType(true, 8))
    assertSAT(script + "\n(check-sat)")
  }

  test("unsupported features") {
    intercept[tip.MissformedTIPException] {
      parse("(declare-const f (-> (! Int :var n :implicit) (BitVec n) (BitVec n)))\n(check-sat)")
    }
    intercept[tip.MissformedTIPException] {
      parse("(declare-const f (-> (! Int :var n) (BitVec n)))\n(check-sat)")
    }
  }
}
