/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package smtlib3

import org.scalatest.funsuite.AnyFunSuite

import java.io.StringReader

class ParserSuite extends AnyFunSuite {
  import inox.trees._
  import solvers._

  given ctx: Context = TestContext(Options(Seq(
    optSelectedSolvers(Set(
      if (SolverFactory.hasNativeZ3) "nativez3"
      else if (SolverFactory.hasZ3) "smt-z3"
      else "princess")),
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
    if (res.isSAT) "sat" else if (res.isUNSAT) "unsat" else {
      "unknown: " + ctx.reporter.asInstanceOf[TestSilentReporter].lastErrors.mkString("\n")
    }
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

    // types without parameters are uninterpreted, so they may be finite
    assert(typeOf("(declare-type U ())\n(declare-const a U)\n(assert (= a a))", "a").isInstanceOf[TypeParameter])
    assertUNSAT(
      """(declare-type U ())
        |(declare-const a U)
        |(declare-const b U)
        |(define-fun swap ((x U)) U (ite (= x a) b a))
        |(assert (not (= a b)))
        |(assert (forall ((x U)) (or (= x a) (= x b))))
        |(assert (not (= (swap (swap a)) a)))
        |(check-sat)""".stripMargin)
    assertSAT(
      """(declare-sort U 0)
        |(declare-const a U)
        |(declare-const b U)
        |(define-fun other ((x U)) U b)
        |(assert (not (= (other a) a)))
        |(check-sat)""".stripMargin)
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
  }

  test("declare-fun with named parameters") {
    // the result of `above` depends on its parameter
    val above = "(declare-fun above ((x Int)) (! Int :var v :restrict (> v x)))\n"
    assertUNSAT(above +
      """(assert (<= (above 3) 3))
        |(check-sat)""".stripMargin)

    assertSAT(above +
      """(assert (and (= (above 3) 4) (= (above 4) 7)))
        |(check-sat)""".stripMargin)

    assertUNSAT(
      """(declare-fun (par (T) (pick ((x T) (y T)) (! T :var v :restrict (or (= v x) (= v y))))))
        |(assert (not (or (= (pick 1 2) 1) (= (pick 1 2) 2))))
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

  test("tuples and dependent tuples") {
    val plain = "(declare-const p (Tuple Int Bool))\n(assert (= p (tuple 1 true)))"
    assert(typeOf(plain, "p") == TupleType(Seq(IntegerType(), BooleanType())))
    assertSAT(plain + "\n(check-sat)")

    val dependent =
      """(declare-const p (Tuple (! Int :var n) (! Int :var m :restrict (> m n))))
        |(assert (<= ((_ tuple.select 1) p) ((_ tuple.select 0) p)))""".stripMargin
    typeOf(dependent, "p") match {
      case SigmaType(Seq(_), RefinementType(_, pred)) =>
        assert(exprOps.variablesOf(pred).exists(_.id.name == "n"), s"second component doesn't depend on n: $pred")
      case tpe => fail(s"unexpected type $tpe")
    }
    assertUNSAT(dependent + "\n(check-sat)")
    assertSAT("(declare-const p (Tuple (! Int :var n) (! Int :var m :restrict (> m n))))\n" +
      "(assert (= ((_ tuple.select 0) p) 3))\n(check-sat)")
  }

  test("dependent datatype fields") {
    val interval =
      """(declare-datatype Interval ((mk (lo Int) (hi (! Int :var h :restrict (<= lo h))))))
        |(declare-const i Interval)
        |""".stripMargin
    assertUNSAT(interval + "(assert (< (hi i) (lo i)))\n(check-sat)")
    assertUNSAT(interval + "(assert (= i (mk 3 1)))\n(check-sat)")
    assertSAT(interval + "(assert (= i (mk 1 3)))\n(check-sat)")

    val (program, _) = parseOne(interval + "(assert (= (lo i) 0))\n(check-sat)")
    val Seq(sort) = program.symbols.sorts.values.toSeq: @unchecked
    assert(sort.flags.isEmpty, "dependent fields shouldn't need an invariant")
    sort.constructors.head.fields.last.tpe match {
      case RefinementType(_, pred) => assert(exprOps.variablesOf(pred).exists(_.id.name == "lo"))
      case tpe => fail(s"unexpected field type $tpe")
    }
  }

  test("datatype fields refining their selectors") {
    val sorted =
      """(declare-datatype SList ((snil) (scons (hd Int) (tl (! SList :var t :restrict (=> ((_ is scons) t) (< hd (hd t))))))))
        |(declare-const l SList)
        |""".stripMargin
    assertUNSAT(sorted + "(assert (and ((_ is scons) l) ((_ is scons) (tl l)) (>= (hd l) (hd (tl l)))))\n(check-sat)")
    assertUNSAT(sorted + "(assert (= l (scons 2 (scons 1 snil))))\n(check-sat)")
    assertSAT(sorted + "(assert (= l (scons 1 (scons 2 snil))))\n(check-sat)")

    // datatypes only take type parameters
    intercept[Exception] {
      parse("(declare-datatype Vec (par (E (! Int :var n)) ((vnil) (vcons (head E) (tail (Vec E))))))\n(check-sat)")
    }
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

  test("unsigned bit-vectors") {
    val script = "(declare-const u (! (_ BitVec 8) :unsigned))\n(declare-const s (_ BitVec 8))\n(assert (bvult u (bvadd s #x80)))"
    assert(typeOf(script, "u") == BVType(false, 8))
    assert(typeOf(script, "s") == BVType(true, 8))

    // the operations follow their SMT-LIB semantics whatever the signedness of their operands
    assertUNSAT(
      """(declare-const u (! (_ BitVec 8) :unsigned))
        |(declare-const s (_ BitVec 8))
        |(assert (or (bvult u #x00) (bvult s #x00)
        |            (not (= (bvudiv #xFE #x02) #x7F)) (not (= (bvsdiv (! #xFE :unsigned) #x02) (! #xFF :unsigned)))
        |            (not (= (! #xFF :unsigned) (! (! #xFF :unsigned) :signed)))
        |            (not (= ((_ zero_extend 8) #xFF) #x00FF)) (not (= ((_ sign_extend 8) (! #xFF :unsigned)) #xFFFF))
        |            (not (= ((_ extract 7 4) #xA5) #xA)) (not (= (bv2nat #xFF) 255)) (not (= (bvsmod #xF9 #x02) #x01))))
        |(check-sat)""".stripMargin)
  }

  test("characters and unit") {
    val script = "(declare-const c Char)\n(declare-const u UnitTuple)\n(assert (and (= c (! #x0041 :char)) (= u tuple.unit)))"
    assert(typeOf(script, "c") == CharType())
    assert(typeOf(script, "u") == UnitType())
    assertSAT(script + "\n(check-sat)")
  }

  test("integer division is euclidean") {
    assertUNSAT(
      """(assert (or (not (= (div (- 7) 2) (- 4))) (not (= (div (- 7) (- 2)) 4)) (not (= (div 7 (- 2)) (- 3)))
        |            (not (= (mod (- 7) 2) 1))))
        |(check-sat)""".stripMargin)
  }

  test("custom datatype equality") {
    val frac =
      """(declare-datatype Frac ((frac (num Int) (den (! Int :var d :restrict (> d 0))))))
        |(define-fun same ((a Frac) (b Frac)) Bool (= (* (num a) (den b)) (* (num b) (den a))))
        |(datatype-equality Frac same)
        |(declare-const a Frac)
        |(declare-const b Frac)
        |""".stripMargin
    assertUNSAT(frac + "(assert (and (= (num a) 1) (= (den a) 2) (= (num b) 2) (= (den b) 4) (not (= a b))))\n(check-sat)")

    val (program, _) = parseOne(frac + "(assert (= a b))\n(check-sat)")
    val Seq(sort) = program.symbols.sorts.values.toSeq: @unchecked
    assert(sort.flags.exists(_.isInstanceOf[HasADTEquality]))

    intercept[tip.MissformedTIPException] {
      parse(frac.replace("Bool (=", "Int (ite (=").replace("(den a))))", "(den a))) 1 0))") + "(check-sat)")
    }
  }

  test("definitions that refer to declared constants") {
    assertUNSAT(
      """(declare-const a Int)
        |(declare-const b Int)
        |(define-fun sum () Int (+ a b))
        |(define-fun addA ((x Int)) Int (+ x a))
        |(define-const c Int (* 2 a))
        |(assert (= a 1))
        |(assert (= b 2))
        |(assert (or (not (= sum 3)) (not (= (addA 5) 6)) (not (= c 2))))
        |(check-sat)""".stripMargin)

    intercept[tip.MissformedTIPException] {
      parse("(declare-type-var A)\n(declare-const a Int)\n(define-fun f ((x A)) Int a)\n(check-sat)")
    }
  }

  test("push and pop") {
    val queries = Parser(new StringReader(
      """(declare-const a Int)
        |(declare-type-var A)
        |(push 1)
        |(define-fun pos ((x Int)) Bool (> x 0))
        |(define-type Pos () (! Int :var x :restrict (pos x)))
        |(declare-const p Pos)
        |(assert (= a p))
        |(set-info :status unsat)
        |(check-sat)
        |(pop 1)
        |(push 2)
        |(define-fun pos ((x Int)) Bool (< x 0))
        |(assert (pos a))
        |(set-info :status sat)
        |(set-option :feeling-lucky true)
        |(check-sat)
        |(pop 2)
        |(check-sat)""".stripMargin)).parseQueries
    assert(queries.map(_.status) == Seq(Some("unsat"), Some("sat"), Some("sat")))
    assert(queries.map(_.options.get("feeling-lucky")) == Seq(None, Some("true"), Some("true")))
    // the scoped assertions and definitions don't outlive their scope
    assert(queries.map(_.program.symbols.functions.size) == Seq(1, 1, 0))
    assert(queries.last.expr == BooleanLiteral(true))

    intercept[tip.MissformedTIPException] {
      parse("(push 1)\n(pop 2)\n(check-sat)")
    }
  }

  test("annotated types as type arguments") {
    // type checks of sets only terminate for finite values, see TypeUnrollingSuite
    val script = "(declare-const s (Set (! Int :var x :restrict (> x 2))))\n(assert (= s (insert (as emptyset Int) 1)))"
    typeOf(script, "s") match {
      case SetType(RefinementType(_, _)) =>
      case tpe => fail(s"unexpected type $tpe")
    }
    assertUNSAT(script + "\n(check-sat)")
    assertSAT("(declare-const m (Array Int (! Int :var x :restrict (> x 2))))\n(assert (= (select m 0) 3))\n(check-sat)")
    assertUNSAT(
      """(declare-datatypes ((List 1)) ((par (E) ((nil) (cons (head E) (tail (List E)))))))
        |(declare-const l (List (! Int :var x :restrict (> x 0))))
        |(assert (and ((_ is cons) l) (= (head l) 0)))
        |(check-sat)""".stripMargin)
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
