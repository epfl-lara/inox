/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

import org.scalatest.funsuite.AnyFunSuite

/** The replay of the steps that rewrite the solver's input into the sources. */
class SimplificationsSuite extends AnyFunSuite {
  import Checker._

  def term(text: String): SExpr = parse(text).head

  val definitions: List[SExpr] = parse(
    """(declare-datatypes ((List 0)) (((Nil) (Cons (head Int) (tail List)))))
      |(define-fun f ((y Int)) Bool (and (> y 0) true))""".stripMargin)

  /** Checks that `steps` rewrite `original` into the expression `simplified`. */
  def check(original: String, simplified: String, steps: String, equality: String = "none"): Either[String, List[String]] =
    try Right(Simplifications.check(
      List(term(s"(function-equality $equality)"), term(s"(expression 0 $original (names) $steps)")),
      definitions, i => if (i == 0) Some(term(simplified)) else None))
    catch { case e: Failure => Left(e.getMessage) }

  def holds(original: String, simplified: String, steps: String, equality: String = "none"): Unit =
    assert(check(original, simplified, steps, equality) == Right(Nil))

  /** The steps are accepted, with one report of what isn't checked. */
  def reported(original: String, simplified: String, steps: String, equality: String = "none"): Unit =
    check(original, simplified, steps, equality) match {
      case Right(List(report)) => info(report)
      case other => fail(s"the steps were not reported: $other")
    }

  def refused(original: String, simplified: String, steps: String, equality: String = "none"): Unit =
    check(original, simplified, steps, equality) match {
      case Left(why) => info(why)
      case other => fail(s"the steps were accepted: $other")
    }

  test("An unfolded call simplifies by logic") {
    holds("(and (f x) true)", "(> x 0)",
      "(steps (unfold (1) (let ((y x)) (and (> y 0) true))) (expand (1 2 1 1) x) (logic () (> x 0)))")
  }

  test("A step is told by the term that it gives, and the rule must give it") {
    refused("(and (f x) true)", "(> x 1)", "(steps (unfold (1) (let ((y x)) (> y 1))) (logic () (> x 1)))")
    refused("(and (f x) true)", "(> x 0)", "(steps (beta (1) (let ((y x)) (and (> y 0) true))) (logic () (> x 0)))")
  }

  test("Logic that drops a disjunct is refused") {
    refused("(or p q)", "p", "(steps (logic () p))")
  }

  test("Logic may drop an assumption, which only refines") {
    holds("(assume p q)", "q", "(steps (logic () q))")
  }

  test("Logic uses the facts of the path") {
    holds("(and p (or p q))", "p", "(steps (logic () p))")
    holds("(ite p (and p q) r)", "(ite p q r)", "(steps (logic (2) q))")
    refused("(ite p r (and p q))", "(ite p r q)", "(steps (logic (3) q))")
  }

  test("Steps are not checked when functions are compared") {
    val original = "(lambda ((x Int)) (assume (> x 0) (> x 1)))"
    val simplified = "(lambda ((x Int)) (> x 1))"
    holds(original, simplified, "(steps (logic (2) (> x 1)))")
    reported(original, simplified, "(steps (logic (2) (> x 1)))", equality = "extensional")
  }

  test("A variable expands to the value of its let") {
    holds("(let ((y (+ x 1))) (> y 0))", "(> (+ x 1) 0)",
      "(steps (expand (2 1) (+ x 1)) (logic () (> (+ x 1) 0)))")
    refused("(let ((y (+ x 1))) (> y 0))", "(> (+ x 2) 0)",
      "(steps (expand (2 1) (+ x 2)) (logic () (> (+ x 2) 0)))")
  }

  test("Terms are the same up to the names of bound variables, without capture") {
    holds("(forall ((x Int)) (> x y))", "(forall ((z Int)) (> z y))", "(steps)")
    refused("(forall ((x Int)) (> x y))", "(forall ((y Int)) (> y y))", "(steps)")
  }

  test("A selector of a construction selects its field") {
    holds("(head (Cons x Nil))", "x", "(steps (select () x))")
    refused("(head (tail (Cons x Nil)))", "x", "(steps (select () x))")
  }

  test("A quantifier over true is dropped") {
    holds("(and p (forall ((x Int)) true))", "p", "(steps (unused (2) true) (logic () p))")
    refused("(and p (forall ((x Int)) q))", "p", "(steps (unused (2) true) (logic () p))")
  }

  test("A quantifier loses the variables that its body doesn't mention") {
    holds("(forall ((x Int) (y Int)) (> x 0))", "(forall ((x Int)) (> x 0))", "(steps (unused () (forall ((x Int)) (> x 0))))")
    refused("(forall ((x Int) (y Int)) (> x y))", "(forall ((x Int)) (> x y))", "(steps (unused () (forall ((x Int)) (> x y))))")
  }

  test("A quantifier comes out of a conclusion, and not of a premise") {
    holds("(forall ((x Int)) (=> (> x 0) (forall ((y Int)) (> y x))))", "(forall ((x Int) (y Int)) (=> (> x 0) (> y x)))",
      "(steps (prenex () (forall ((x Int) (y Int)) (=> (> x 0) (> y x)))))")
    refused("(forall ((x Int)) (=> (forall ((y Int)) (> y x)) (> x 0)))", "(forall ((x Int) (y Int)) (=> (> y x) (> x 0)))",
      "(steps (prenex () (forall ((x Int) (y Int)) (=> (> y x) (> x 0)))))")
  }

  test("Some of the quantifiers of a connective may stay") {
    // the one of the premise stays, and the one of the conclusion comes out
    holds("(forall ((x Int)) (=> (forall ((y Int)) (> y x)) (forall ((z Int)) (> z x))))",
      "(forall ((x Int) (z Int)) (=> (forall ((y Int)) (> y x)) (> z x)))",
      "(steps (prenex () (forall ((x Int) (z Int)) (=> (forall ((y Int)) (> y x)) (> z x)))))")
    // a quantifier over a sort that may be empty stays
    holds("(forall ((x Int)) (and (forall ((y T)) p) (forall ((z Int)) (> z x))))",
      "(forall ((x Int) (z Int)) (and (forall ((y T)) p) (> z x)))",
      "(steps (prenex () (forall ((x Int) (z Int)) (and (forall ((y T)) p) (> z x)))))")
    refused("(forall ((x Int)) (and (forall ((y T)) p) (> x 0)))", "(forall ((x Int) (y T)) (and p (> x 0)))",
      "(steps (prenex () (forall ((x Int) (y T)) (and p (> x 0)))))")
  }

  test("Arithmetic is that of polynomials") {
    holds("(> (+ x (- y x)) 0)", "(> y 0)", "(steps (arith (1) y))")
    holds("(= (+ x 1) (+ 1 x))", "true", "(steps (arith () true))")
    holds("(= (+ x 1) x)", "false", "(steps (arith () false))")
    refused("(> (+ x y) 0)", "(> (+ x x) 0)", "(steps (arith (1 2) x))")
    refused("(= x y)", "false", "(steps (arith () false))")
  }

  test("A let lifts out of an operand that is always evaluated") {
    holds("(> (let ((y (+ x 1))) y) 0)", "(let ((y (+ x 1))) (> y 0))", "(steps (lift () (let ((y (+ x 1))) (> y 0))))")
    refused("(or p (let ((y q)) y))", "(let ((y q)) (or p y))", "(steps (lift () (let ((y q)) (or p y))))")
  }

  test("A position is one of the term") {
    refused("(and p q)", "p", "(steps (logic (3) p))")
    refused("(and p q)", "p", "(steps (logic (x) p))")
  }

  test("Steps that don't end at the source are refused") {
    refused("(and p q)", "p", "(steps)")
    refused("(and p (or p q))", "q", "(steps (logic () p))")
  }

  test("Terms whose variables are bound by other binders are not the same") {
    refused("(forall ((x Int)) (forall ((a Int)) (> x 0)))", "(forall ((y Int)) (forall ((y Int)) (> y 0)))", "(steps)")
    holds("(forall ((x Int)) (forall ((a Int)) (> a 0)))", "(forall ((y Int)) (forall ((y Int)) (> y 0)))", "(steps)")
  }

  test("Quantifiers that bind the same variable don't merge") {
    refused("(forall ((x Int)) (forall ((x Int)) (> x 0)))", "(forall ((x Int) (x Int)) (> x 0))", "(steps (merge () (forall ((x Int) (x Int)) (> x 0))))")
    holds("(forall ((x Int)) (forall ((y Int)) (> x y)))", "(forall ((x Int) (y Int)) (> x y))", "(steps (merge () (forall ((x Int) (y Int)) (> x y))))")
  }

  def named(original: String, simplified: String, names: String): Either[String, List[String]] =
    try Right(Simplifications.check(
      List(term("(function-equality none)"), term(s"(expression 0 $original (names $names) (steps))")),
      definitions, i => if (i == 0) Some(term(simplified)) else None))
    catch { case e: Failure => Left(e.getMessage) }

  test("A name is a symbol that the solver made, and not one of the original expression") {
    assert(named("(@ (lambda ((z Int)) (> z x)) 1)", "(@ lambda!1 1)", "(lambda!1 (lambda ((z Int)) (> z x)))") == Right(Nil))
    assert(named("p", "false", "(false p)").isLeft)
    assert(named("(and p q)", "(and p p)", "(p q)").isLeft)
    assert(named("p", "(f x)", "((f x) p)").isLeft)
    assert(named("(> x 1)", "(> x 0)", "(0 1)").isLeft)
  }

  test("A quantifier is assumed in the source only where it must hold") {
    val q = "(forall ((z Int)) (> z x))"
    assert(named(s"(and p $q)", s"(and p (assume $q true))", s"((assume $q true) $q)") == Right(Nil))
    assert(named(s"(or p $q)", s"(or p (assume $q true))", s"((assume $q true) $q)") == Right(Nil))
    assert(named(s"(or $q p)", s"(or (assume $q true) p)", s"((assume $q true) $q)").isLeft)
    assert(named(s"(not $q)", s"(not (assume $q true))", s"((assume $q true) $q)").isLeft)
    assert(named("(and p q)", "(and p (assume q true))", "((assume q true) r)").isLeft)
  }

  test("The steps of the body of a function are not checked when functions are compared") {
    def body(equality: String) =
      try Right(Simplifications.check(
        List(term(s"(function-equality $equality)"), term("(function f (assume (> y 1) (and (> y 0) true)) (steps (logic () (and (> y 0) true))))")),
        definitions, _ => None))
      catch { case e: Failure => Left(e.getMessage) }
    assert(body("none") == Right(Nil))
    assert(body("extensional").exists(_.size == 1))
  }

  test("A step of a rule that the checker doesn't know is reported, and the others are checked") {
    // the certificate then holds over the simplified program
    reported("(and p q)", "p", "(steps (evaluate () p))")
    reported("(and (and p q) (or p r))", "p", "(steps (evaluate (1) p) (logic () p))")
    // what a simplifier did without recording it is refused
    refused("(and p q)", "p", "(steps (unrecorded () p))")
    // the steps of the rules that it knows must still hold
    refused("(and (and p q) (or p r))", "r", "(steps (evaluate (1) p) (logic () r))")
    // and the steps must end at the source
    refused("(and p q)", "p", "(steps (evaluate () q))")
    refused("(and p q)", "p", "(steps (evaluate (7) p))")
  }
}
