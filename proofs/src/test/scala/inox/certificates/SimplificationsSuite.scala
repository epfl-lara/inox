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
      |(define-fun f ((y Int)) Bool (and (> y 0) true))
      |(define-fun-rec len ((l List)) Int (ite ((_ is Cons) l) (+ 1 (len (tail l))) 0))
      |(define-fun twice ((y Int)) Int (double y))
      |(define-fun double ((y Int)) Int (+ y y))
      |(define-fun-rec loop ((y Int)) Int (loop y))
      |(declare-datatypes ((Pos 0)) (((pos (pv Int)))))
      |(datatype-invariant q Pos (positive (pv q)))
      |(define-fun positive ((y Int)) Bool (> y 0))
      |(define-fun inv ((r Pos)) Bool (positive (pv r)))
      |(declare-datatypes ((Box 0)) (((box (get (-> Int Bool))))))
      |(define-fun single ((a Int)) Box (box (lambda ((z Int)) (= z a))))
      |(define-fun both ((b Box) (c Box)) Box (box (lambda ((z Int)) (or (@ (get b) z) (@ (get c) z)))))""".stripMargin)

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

  test("What a simplifier makes of a term without a rule is checked where it is a step of logic") {
    holds("(let ((v (len l))) (> x 0))", "(> x 0)", "(steps (simplify () (> x 0)))")
    reported("(> x 0)", "(let ((v (loop 0))) (> x 0))", "(steps (simplify () (let ((v (loop 0))) (> x 0))))")
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

  test("An evaluation of a closed term gives its value in the semantics") {
    holds("(and p (> (+ 1 2) 2))", "p", "(steps (evaluate (2) true) (logic () p))")
    holds("(= x (ite true 5 0))", "(= x 5)", "(steps (evaluate (2) 5))")
    // with the functions of the source definitions
    holds("(= x (len (Cons 1 (Cons 2 Nil))))", "(= x 2)", "(steps (evaluate (2) 2))")
    holds("(and p (f 1))", "p", "(steps (evaluate (2) true) (logic () p))")
    // which the certificate may define after the ones that call them, and write the sorts of
    holds("(= x (twice 2))", "(= x 4)", "(steps (evaluate (2) 4))")
    holds("(= x ((as head List) (Cons 1 Nil)))", "(= x 1)", "(steps (evaluate (2) 1))")
    holds("(and p ((as (_ is Cons) List) (Cons 1 Nil)))", "p", "(steps (evaluate (2) true) (logic () p))")
    // another value than the one of the term is refused
    refused("(and p (> (+ 1 2) 2))", "(and p false)", "(steps (evaluate (2) false))")
    refused("(= x (len (Cons 1 (Cons 2 Nil))))", "(= x 3)", "(steps (evaluate (2) 3))")
    refused("(= x (ite true 5 0))", "(= x 0)", "(steps (evaluate (2) 0))")
    // a term that has no value within the fuel, or that isn't closed, is reported
    reported("(= x (loop 0))", "(= x 0)", "(steps (evaluate (2) 0))")
    reported("(= x (+ y 0))", "(= x y)", "(steps (evaluate (2) y))")
  }

  test("An evaluation is over the program before its simplifications") {
    // `f` is simplified by a step that the checker doesn't know, into a body of another value
    def check(simplified: String, steps: String) =
      try Right(Simplifications.check(
        List(term("(function-equality none)"), term("(function f (and (> y 0) false) (steps (fold () (and (> y 0) true))))"),
          term(s"(expression 0 (and p (f 1)) (names) $steps)")),
        definitions, i => if (i == 0) Some(term(simplified)) else None))
      catch { case e: Failure => Left(e.getMessage) }
    // the call has the value of the original body
    assert(check("false", "(steps (evaluate (2) false) (logic () false))").exists(_.size == 1))
    assert(check("p", "(steps (evaluate (2) true) (logic () p))").isLeft)
  }

  test("Literals that are written differently may be the same value") {
    refused("(= #x0a #x0A)", "false", "(steps (arith () false))")
    refused("(= #x0a #b00001010)", "false", "(steps (arith () false))")
    refused("(= \"a\" \"\\u{61}\")", "false", "(steps (arith () false))")
    holds("(= #x0a #x0b)", "false", "(steps (arith () false))")
    holds("(= \"a\" \"b\")", "false", "(steps (arith () false))")
  }

  test("A construction of the fields of a term is the term, where it is of the constructor") {
    holds("(ite ((_ is Cons) l) (Cons (head l) (tail l)) l)", "(ite ((_ is Cons) l) l l)", "(steps (eta (2) l))")
    // which it is when it is of no other constructor
    holds("(ite ((_ is Nil) l) l (Cons (head l) (tail l)))", "(ite ((_ is Nil) l) l l)", "(steps (eta (3) l))")
    refused("(ite p (Cons (head l) (tail l)) l)", "(ite p l l)", "(steps (eta (2) l))")
    refused("(ite ((_ is Cons) l) (Cons (head l) (head l)) l)", "(ite ((_ is Cons) l) l l)", "(steps (eta (2) l))")
  }

  test("Sums and products are those of their operands, however they nest") {
    holds("(> (* (* x y) z) 0)", "(> (* x y z) 0)", "(steps (logic () (> (* x y z) 0)))")
    holds("(and p (> (+ x (+ y z)) 0))", "(and p (> (+ x y z) 0))", "(steps (logic () (and p (> (+ x y z) 0))))")
    refused("(> (* (+ x y) z) 0)", "(> (* x y z) 0)", "(steps (logic () (> (* x y z) 0)))")
  }

  test("Logic evaluates the conditionals, bindings and assumptions of the operands of an atom") {
    holds("(let ((r (ite p x y))) (> r 0))", "(> (ite p x y) 0)", "(steps (logic () (> (ite p x y) 0)))")
    holds("(> (ite p x y) 0)", "(ite p (> x 0) (> y 0))", "(steps (logic () (ite p (> x 0) (> y 0))))")
    holds("(> (assume p x) 0)", "(assume p (> x 0))", "(steps (logic () (assume p (> x 0))))")
    holds("(assume p (> x 0))", "(> (assume p x) 0)", "(steps (logic () (> (assume p x) 0)))")
    // an assumption that the term doesn't make is not one that a step may add
    refused("(> x 0)", "(> (assume p x) 0)", "(steps (logic () (> (assume p x) 0)))")
    refused("(> (ite p x y) 0)", "(> x 0)", "(steps (logic () (> x 0)))")
  }

  test("Logic evaluates what a quantifier evaluates for all values, where it has values") {
    holds("(let ((v (assume p x))) (exists ((k Int)) (= v k)))", "(exists ((k Int)) (= (assume p x) k))",
      "(steps (logic () (exists ((k Int)) (= (assume p x) k))))")
    // a quantifier whose body always evaluates an assumption that doesn't hold has no value
    holds("(exists ((k Int)) (= (assume p x) k))", "(assume p (exists ((k Int)) (= x k)))",
      "(steps (lift-assumptions () (assume p (exists ((k Int)) (= x k)))))")
    holds("(assume p (exists ((k Int)) (= x k)))", "(exists ((k Int)) (= (assume p x) k))",
      "(steps (logic () (exists ((k Int)) (= (assume p x) k))))")
    // unless it has no values to evaluate it for, or doesn't always evaluate it
    refused("(forall ((k T)) (= (assume p x) (g k)))", "(assume p (forall ((k T)) (= x (g k))))",
      "(steps (logic () (assume p (forall ((k T)) (= x (g k))))))")
    refused("(forall ((k Int)) (or (> k 0) (= (assume p x) k)))", "(assume p (forall ((k Int)) (or (> k 0) (= x k))))",
      "(steps (logic () (assume p (forall ((k Int)) (or (> k 0) (= x k))))))")
  }

  test("An assumption that is lifted out of a binder is checked where it is a step of logic, and reported otherwise") {
    holds("(forall ((k Int)) (= (assume p x) k))", "(assume p (forall ((k Int)) (= x k)))",
      "(steps (lift-assumptions () (assume p (forall ((k Int)) (= x k)))))")
    reported("(forall ((k Int)) (or (> k 0) (= (assume p x) k)))", "(assume p (forall ((k Int)) (or (> k 0) (= x k))))",
      "(steps (lift-assumptions () (assume p (forall ((k Int)) (or (> k 0) (= x k))))))")
    reported("(= h (lambda ((k Int)) (+ (assume p x) k)))", "(assume p (= h (lambda ((k Int)) (+ x k))))",
      "(steps (lift-assumptions () (assume p (= h (lambda ((k Int)) (+ x k))))))")
  }

  test("A quantifier comes out of the last operand of a disjunction only") {
    // `(forall y. p)` may be false for some `y` and stuck for another, where `q` holds
    refused("(forall ((x Int)) (or (forall ((y Int)) (assume (> y x) p)) q))", "(forall ((x Int) (y Int)) (or (assume (> y x) p) q))",
      "(steps (prenex () (forall ((x Int) (y Int)) (or (assume (> y x) p) q))))")
    holds("(forall ((x Int)) (or q (forall ((y Int)) (assume (> y x) p))))", "(forall ((x Int) (y Int)) (or q (assume (> y x) p)))",
      "(steps (prenex () (forall ((x Int) (y Int)) (or q (assume (> y x) p)))))")
  }

  test("A quantifier comes out of a disjunction over a sort that may have no values") {
    holds("(forall ((x Int)) (or (> x 0) (forall ((y T)) p)))", "(forall ((x Int) (y T)) (or (> x 0) p))",
      "(steps (prenex () (forall ((x Int) (y T)) (or (> x 0) p))))")
    holds("(forall ((x Int)) (=> (> x 0) (forall ((y T)) p)))", "(forall ((x Int) (y T)) (=> (> x 0) p))",
      "(steps (prenex () (forall ((x Int) (y T)) (=> (> x 0) p))))")
  }

  test("An existential quantifier is named as the negation of the universal one that is assumed") {
    val (all, some) = ("(forall ((z Int)) (not (> z x)))", "(exists ((z Int)) (> z x))")
    assert(named(s"(not (and p $some))", s"(not (and p (not (assume $all true))))", s"((not (assume $all true)) $some)") == Right(Nil))
    // only where the universal one must hold
    assert(named(s"(and p $some)", s"(and p (not (assume $all true)))", s"((not (assume $all true)) $some)").isLeft)
    assert(named(s"(not (or p $some))", s"(not (or p (not (assume $all true))))", s"((not (assume $all true)) $some)") == Right(Nil))
    assert(named(s"(or p $some)", s"(or p (not (assume $all true)))", s"((not (assume $all true)) $some)").isLeft)
    // and of the same body
    assert(named(s"(not (and p (exists ((z Int)) (> z 0))))", s"(not (and p (not (assume $all true))))",
      s"((not (assume $all true)) (exists ((z Int)) (> z 0)))").isLeft)
  }

  test("A construction is named under the assumption of its invariant, which is evaluated") {
    val cons = "(Cons 1 Nil)"
    def name(invariant: String) = named(s"(= l $cons)", s"(= l (assume $invariant $cons))", s"((assume $invariant $cons) $cons)")
    assert(name("(> (len (Cons 1 Nil)) 0)") == Right(Nil))
    assert(name("(> (len (Cons 1 Nil)) 1)").isLeft)
    // an invariant that has no value in the semantics is reported
    assert(name("(> (len l) 0)").exists(_.size == 1))
    // and the assumption is around the construction that it names
    assert(named(s"(= l $cons)", "(= l (assume true Nil))", s"((assume true Nil) $cons)").isLeft)
  }

  test("A construction is named under the invariant of its sort") {
    def name(invariant: String) = named("(= u (pos x))", s"(= u (assume $invariant (pos x)))", s"((assume $invariant (pos x)) (pos x))")
    // as the sort states it of the construction, whose selections are its fields
    assert(name("(positive x)") == Right(Nil))
    // or as a function of the same body does
    assert(name("(inv (pos x))") == Right(Nil))
    // another assumption is reported
    assert(name("(> x 5)").exists(_.size == 1))
    assert(name("(positive y)").exists(_.size == 1))
  }

  test("An evaluation of a construction is that of the invariant of its sort") {
    holds("(= x (pv (pos 1)))", "(= x 1)", "(steps (evaluate (2) 1))")
    // a construction whose invariant doesn't hold has no value, which the field of a selection refines
    holds("(= x (pv (pos 0)))", "(= x 0)", "(steps (evaluate (2) 0))")
    reported("(= u (pos 0))", "(= u (pos 1))", "(steps (evaluate (2) (pos 1)))")
  }

  test("An evaluation to a function gives the lambda that the term reduces to") {
    val (one, two) = ("(lambda ((z Int)) (= z 1))", "(lambda ((z Int)) (= z 2))")
    holds("(= u (single 1))", s"(= u (box $one))", s"(steps (evaluate (2) (box $one)))")
    // a selection of a construction of values is its field, under the lambda too
    val or = s"(box (lambda ((z Int)) (or (@ $one z) (@ $two z))))"
    holds("(= u (both (single 1) (single 2)))", s"(= u $or)", s"(steps (evaluate (2) $or))")
    holds("(= u (let ((s (single 1))) (get s)))", s"(= u $one)", s"(steps (evaluate (2) $one))")
    // another lambda is not known to be the value, nor is a term that is not a value
    reported("(= u (single 1))", s"(= u (box $two))", s"(steps (evaluate (2) (box $two)))")
    reported("(= u (single 1))", "(= u (single (+ 0 1)))", "(steps (evaluate (2) (single (+ 0 1))))")
    // and a term with variables doesn't reduce
    reported("(= u (single x))", "(= u (box (lambda ((z Int)) (= z x))))", "(steps (evaluate (2) (box (lambda ((z Int)) (= z x)))))")
  }
}
