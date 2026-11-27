/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import org.scalatest.funsuite.AnyFunSuite

import _root_.smtlib.lexer.Lexer
import _root_.smtlib.parser.Parser
import _root_.smtlib.trees.{Commands => SC, CommandsResponses => SR, Terms => ST}

/** Reads models that Z3 and CVC4 gave in other versions or for other queries than the solver
  * suites make. Each solver here answers its commands without a solver process: every check is
  * satisfiable, and `get-model` answers with the given model text. */
class ModelParsingSuite extends AnyFunSuite {
  import inox.trees.{given, *}
  import inox.trees.dsl.{given, *}
  import SolverResponses.*

  val listID = FreshIdentifier("List")
  val nilID = FreshIdentifier("Nil")
  val consID = FreshIdentifier("Cons")
  val headID = FreshIdentifier("head")
  val tailID = FreshIdentifier("tail")
  val listSort = mkSort(listID)() { _ => Seq(
    (nilID, Seq()),
    (consID, Seq(ValDef(headID, IntegerType()), ValDef(tailID, T(listID)()))))
  }
  val listType = T(listID)()

  val prog = InoxProgram(NoSymbols.withSorts(Seq(listSort)))
  given prog.Semantics = prog.getSemantics
  val ctx = TestContext.empty

  def z3Parser(text: String): Parser =
    new Z3Target.Z3Parser(new _root_.smtlib.extensions.tip.Lexer(new java.io.StringReader(text)))

  /** A solver that answers every command, with a model built from its names for the query. */
  trait Answering extends SMTLIBSolver {
    import this.program.trees.*

    var model: String = ""

    /** The parser of the solver's answers. */
    def parser(text: String): Parser = new Parser(new Lexer(new java.io.StringReader(text)))

    override def emit(cmd: ST.SExpr, rawOut: Boolean): ST.SExpr = cmd match {
      case _: SC.CheckSat | _: SC.CheckSatAssuming => SR.CheckSatStatus(SR.SatStatus)
      case _: SC.GetModel => parser(model).parseGetModelResponse
      case SC.GetInfo(_: SC.VersionInfoFlag) => SR.GetInfoResponseSuccess(SR.VersionInfoResponse("4.8.17"), Seq())
      case ST.SList(List(ST.SSymbol("check-sat"), _*)) => ST.SSymbol("sat")
      case _ => SR.Success
    }

    override def free(): Unit = ()

    def nameOf(v: Variable): String = variables.toB(v).name
    def constructorOf(id: Identifier): String = constructors.toB(ADTCons(id, Seq())).name
    def testerOf(id: Identifier): String = testers.toB(ADTCons(id, Seq())).name
    def selectorOf(id: Identifier, i: Int): String = selectors.toB((ADTCons(id, Seq()), i)).name
    def sortOf(tpe: Type): String = declareSort(tpe).id.symbol.name
  }

  class Z3(override val program: prog.type) extends SMTLIBSolver(program, ctx) with Z3Solver with Answering {
    override protected val interpreter: PipelinedZ3Interpreter = null
    override def parser(text: String): Parser = z3Parser(text)
  }

  class CVC4(override val program: prog.type) extends SMTLIBSolver(program, ctx) with CVC4Solver with Answering {
    override protected val interpreter: _root_.smtlib.interpreters.ProcessInterpreter = null
  }

  type Solver = Answering { val program: prog.type }

  /** The values that `solver` reads from the model `text` for a query about `vars`, which leaves
    * out the values that it can't read. */
  def modelOf(solver: Solver, vars: Variable*)(text: solver.type => String): Map[Variable, Expr] = {
    for (v <- vars) solver.assertCnstr(Equals(v, v))
    solver.model = "(" + text(solver) + ")"
    solver.check(Model) match {
      case SatWithModel(model) => vars.flatMap(v => model.vars.get(v.toVal).map(v -> _)).toMap
      case res => fail(s"Expected a model, got $res")
    }
  }

  def valueOf(solver: Solver, v: Variable)(text: solver.type => String): Expr =
    modelOf(solver, v)(text).getOrElse(v, fail(s"The model has no value for $v"))

  def z3 = new Z3(prog)
  def cvc4 = new CVC4(prog)

  val i = Variable.fresh("i", IntegerType())
  val b = Variable.fresh("b", BooleanType())
  val l = Variable.fresh("l", listType)
  val str = Variable.fresh("s", StringType())
  val c = Variable.fresh("c", CharType())
  val m = Variable.fresh("m", MapType(IntegerType(), IntegerType()))
  val mb = Variable.fresh("mb", MapType(IntegerType(), BooleanType()))
  val set = Variable.fresh("set", SetType(IntegerType()))
  val bag = Variable.fresh("bag", BagType(IntegerType()))

  def cons(h: BigInt, t: Expr): Expr = ADT(consID, Seq(), Seq(IntegerLiteral(h), t))
  val nil: Expr = ADT(nilID, Seq(), Seq())
  def intMap(pairs: (Int, Int)*)(default: Int): Expr =
    FiniteMap(pairs.map(p => IntegerLiteral(p._1) -> IntegerLiteral(p._2)), IntegerLiteral(default), IntegerType(), IntegerType())
  def intSet(elems: Int*): Expr = FiniteSet(elems.map(IntegerLiteral(_)), IntegerType())
  def intBag(elems: (Int, Int)*): Expr = FiniteBag(elems.map(p => IntegerLiteral(p._1) -> IntegerLiteral(p._2)), IntegerType())

  /** Whether `e` is the given finite map, set or bag, in any order of its elements. */
  def sameElements(e: Expr, expected: Expr): Boolean = (e, expected) match {
    case (FiniteMap(es1, d1, _, _), FiniteMap(es2, d2, _, _)) => es1.toSet == es2.toSet && d1 == d2
    case (FiniteSet(es1, _), FiniteSet(es2, _)) => es1.toSet == es2.toSet
    case (FiniteBag(es1, _), FiniteBag(es2, _)) => es1.toSet == es2.toSet
    case _ => false
  }

  def assertElements(e: Expr, expected: Expr): Unit =
    assert(sameElements(e, expected), s"Expected $expected, got $e")

  // Z3

  test("Z3 testers of constructors") {
    val s = z3
    val model = modelOf(s, b, l)(s => s"""
      (define-fun ${s.nameOf(b)} () Bool
        ((_ is ${s.constructorOf(consID)}) (${s.constructorOf(consID)} 1 ${s.constructorOf(nilID)})))""")
    assert(model(b) == BooleanLiteral(true))
  }

  test("Z3 unspecified values") {
    val s = z3
    val model = modelOf(s, i)(s => s"(define-fun ${s.nameOf(i)} () Int #unspecified)")
    assert(model.get(i).forall(_.isInstanceOf[UninterpretedCall]), model)
  }

  test("Z3 strings of characters") {
    val s = z3
    assert(valueOf(s, str)(s => s"""(define-fun ${s.nameOf(str)} () String (str.++ (seq.unit (_ Char 97)) "b"))""") ==
      StringLiteral("ab"))
    val t = z3
    assert(valueOf(t, str)(t => s"""(define-fun ${t.nameOf(str)} () String (str.++ "a" "b" "c"))""") == StringLiteral("abc"))
  }

  test("Z3 strings of characters given as bit-vectors") {
    val s = z3
    assert(valueOf(s, str)(s => s"""(define-fun ${s.nameOf(str)} () String (str.++ (seq.unit #x61) (seq.unit #x62)))""") ==
      StringLiteral("ab"))
  }

  test("Z3 unspecified values whose type isn't known") {
    val s = z3
    intercept[MissformedSMTException](modelOf(s, b)(s => s"(define-fun ${s.nameOf(b)} () Bool (= #unspecified 1))"))
  }

  test("Z3 characters") {
    val s = z3
    assert(valueOf(s, c)(s => s"(define-fun ${s.nameOf(c)} () (_ BitVec 16) (_ Char 97))") == CharLiteral('a'))
  }

  test("Z3 maps given by an array function") {
    val s = z3
    assertElements(valueOf(s, m)(s => s"""
      (define-fun ${s.nameOf(m)} () (Array Int Int) (_ as-array k!1))
      (define-fun k!1 ((x!0 Int)) Int (ite (= x!0 1) 2 (ite (= x!0 3) 4 0)))"""), intMap(1 -> 2, 3 -> 4)(0))
    val t = z3
    assertElements(valueOf(t, mb)(t => s"""
      (define-fun ${t.nameOf(mb)} () (Array Int Bool) (_ as-array k!1))
      (define-fun k!1 ((x!0 Int)) Bool (= x!0 1))"""),
      FiniteMap(Seq(IntegerLiteral(1) -> BooleanLiteral(true)), BooleanLiteral(false), IntegerType(), BooleanType()))
  }

  test("Z3 sets and bags given by an array function") {
    val s = z3
    assertElements(valueOf(s, set)(s => s"""
      (define-fun ${s.nameOf(set)} () (Array Int Bool) (_ as-array k!1))
      (define-fun k!1 ((x!0 Int)) Bool (ite (= x!0 1) true (ite (= x!0 2) false false)))"""), intSet(1))
    val t = z3
    assertElements(valueOf(t, bag)(t => s"""
      (define-fun ${t.nameOf(bag)} () (Array Int Int) (_ as-array k!1))
      (define-fun k!1 ((x!0 Int)) Int (ite (= x!0 1) 2 (ite (= x!0 3) 0 0)))"""), intBag(1 -> 2))
  }

  test("Z3 co-finite sets and bags given by an array function are left out") {
    val s = z3
    assert(modelOf(s, set)(s => s"""
      (define-fun ${s.nameOf(set)} () (Array Int Bool) (_ as-array k!1))
      (define-fun k!1 ((x!0 Int)) Bool true)""").isEmpty)
    val t = z3
    assert(modelOf(t, bag)(t => s"""
      (define-fun ${t.nameOf(bag)} () (Array Int Int) (_ as-array k!1))
      (define-fun k!1 ((x!0 Int)) Int 1)""").isEmpty)
  }

  test("Z3 maps, sets and bags given by a lambda") {
    val s = z3
    assertElements(valueOf(s, m)(s => s"(define-fun ${s.nameOf(m)} () (Array Int Int) (lambda ((x Int)) (ite (= x 1) 2 0)))"),
      intMap(1 -> 2)(0))
    val t = z3
    assertElements(valueOf(t, mb)(t => s"(define-fun ${t.nameOf(mb)} () (Array Int Bool) (lambda ((x Int)) (= x 1)))"),
      FiniteMap(Seq(IntegerLiteral(1) -> BooleanLiteral(true)), BooleanLiteral(false), IntegerType(), BooleanType()))
    val u = z3
    assertElements(valueOf(u, set)(u => s"(define-fun ${u.nameOf(set)} () (Array Int Bool) (lambda ((x Int)) (= x 1)))"),
      intSet(1))
    val w = z3
    assertElements(valueOf(w, bag)(w => s"(define-fun ${w.nameOf(bag)} () (Array Int Int) (lambda ((x Int)) (ite (= x 1) 3 0)))"),
      intBag(1 -> 3))
  }

  test("Z3 co-finite sets and bags given by a lambda are left out") {
    val s = z3
    assert(modelOf(s, set)(s => s"(define-fun ${s.nameOf(set)} () (Array Int Bool) (lambda ((x Int)) true))").isEmpty)
    val t = z3
    assert(modelOf(t, bag)(t => s"(define-fun ${t.nameOf(bag)} () (Array Int Int) (lambda ((x Int)) 1))").isEmpty)
  }

  test("Z3 sets and bags given by stores") {
    val s = z3
    assertElements(valueOf(s, set)(s => s"""(define-fun ${s.nameOf(set)} () (Array Int Bool)
      (store (store (store ((as const (Array Int Bool)) false) 1 true) 2 true) 2 false))"""), intSet(1))
    val t = z3
    assertElements(valueOf(t, bag)(t => s"""(define-fun ${t.nameOf(bag)} () (Array Int Int)
      (store (store ((as const (Array Int Int)) 0) 1 2) 1 3))"""), intBag(1 -> 3))
  }

  test("Z3 sets with a membership that isn't a literal") {
    val s = z3
    assertElements(valueOf(s, set)(s => s"""(define-fun ${s.nameOf(set)} () (Array Int Bool)
      (store (store ((as const (Array Int Bool)) false) 1 (= 1 1)) 2 (= 1 2)))"""), intSet(1))
  }

  test("Z3 co-finite sets and bags given by stores are left out") {
    val s = z3
    assert(modelOf(s, set)(s => s"(define-fun ${s.nameOf(set)} () (Array Int Bool) ((as const (Array Int Bool)) true))").isEmpty)
    val t = z3
    assert(modelOf(t, bag)(t => s"(define-fun ${t.nameOf(bag)} () (Array Int Int) ((as const (Array Int Int)) 1))").isEmpty)
  }

  test("Z3 unions and intersections of sets") {
    val s = z3
    assertElements(valueOf(s, set)(s => s"""(define-fun ${s.nameOf(set)} () (Array Int Bool)
      ((_ map (or (Bool Bool) Bool)) (lambda ((x Int)) (= x 1)) (lambda ((x Int)) (= x 2))))"""), intSet(1, 2))
    val t = z3
    assertElements(valueOf(t, set)(t => s"""(define-fun ${t.nameOf(set)} () (Array Int Bool)
      ((_ map and) (lambda ((x Int)) (ite (= x 1) true (= x 2))) (lambda ((x Int)) (= x 2))))"""), intSet(2))
  }

  test("Z3 merges of maps") {
    val s = z3
    assertElements(valueOf(s, m)(s => s"""(define-fun ${s.nameOf(m)} () (Array Int Int)
      ((_ map (ite (Bool Int Int) Int))
        (store ((as const (Array Int Bool)) false) 1 true)
        (store ((as const (Array Int Int)) 0) 1 5)
        ((as const (Array Int Int)) 7)))"""), intMap(1 -> 5)(7))
  }

  test("Z3 version and unsat assumptions answers") {
    def parse(text: String) = z3Parser(text).parseGetUnsatAssumptionsResponse
    assert(parse("unsupported") == SR.Unsupported)
    assert(parse("""(error "no assumptions")""") == SR.Error("no assumptions"))
    assert(parse("(a (not b))") == SR.GetUnsatAssumptionsResponseSuccess(Seq(
      SC.PropLiteral(ST.SSymbol("a"), true), SC.PropLiteral(ST.SSymbol("b"), false))))
  }

  test("Z3 arrays whose type isn't known") {
    val s = z3
    assert(valueOf(s, b)(s => s"""(define-fun ${s.nameOf(b)} () Bool
      (= ((as const (Array Int Int)) 0) (store ((as const (Array Int Int)) 0) 1 0)))""") == BooleanLiteral(true))
  }

  test("Z3 unions of sets whose type isn't known") {
    val s = z3
    assert(modelOf(s, b, set)(s => s"""(define-fun ${s.nameOf(b)} () Bool
      (= ((_ map or) ((as const (Array Int Bool)) false) ((as const (Array Int Bool)) false))
         ((_ map or) ((as const (Array Int Bool)) false) ((as const (Array Int Bool)) false))))""")(b) ==
      BooleanLiteral(true))
    // a co-finite set, or a set that isn't given as a finite map, is left out
    val t = z3
    assert(modelOf(t, b, set)(t => s"""(define-fun ${t.nameOf(b)} () Bool
      (= ((_ map or) ((as const (Array Int Bool)) true) ((as const (Array Int Bool)) false)) ((as const (Array Int Bool)) false)))""").isEmpty)
    val u = z3
    assert(modelOf(u, b, set)(u => s"""(define-fun ${u.nameOf(b)} () Bool
      (= ((_ map or) (store ((as const (Array Int Bool)) false) 1 true) ((as const (Array Int Bool)) false)) ((as const (Array Int Bool)) false)))""").isEmpty)
  }

  // CVC4

  test("CVC4 negative integers as symbols") {
    val s = cvc4
    assert(valueOf(s, i)(s => s"(define-fun ${s.nameOf(i)} () Int -5)") == IntegerLiteral(-5))
  }

  test("CVC4 symbols that aren't integers") {
    val s = cvc4
    intercept[MissformedSMTException](modelOf(s, i)(s => s"(define-fun ${s.nameOf(i)} () Int -x)"))
  }

  test("CVC4 primed constructors and selectors") {
    val s = cvc4
    val model = modelOf(s, l, i) { s =>
      val (cons, nil) = (s.constructorOf(consID), s.constructorOf(nilID))
      s"""(define-fun ${s.nameOf(l)} () ${s.sortOf(listType)} (|$cons'| 1 $nil))
          (define-fun ${s.nameOf(i)} () Int (|${s.selectorOf(consID, 0)}'| ($cons 2 $nil)))"""
    }
    assert(model(l) == cons(1, nil))
    assert(model(i) == ADTSelector(cons(2, nil), headID))
  }

  test("CVC4 bit-vectors as booleans") {
    val s = cvc4
    assert(valueOf(s, b)(s => s"(define-fun ${s.nameOf(b)} () Bool #b1)") == BooleanLiteral(true))
    val t = cvc4
    assert(valueOf(t, b)(t => s"(define-fun ${t.nameOf(b)} () Bool (_ bv0 1))") == BooleanLiteral(false))
  }

  test("CVC4 equalities") {
    val s = cvc4
    val model = modelOf(s, b, i)(s => s"""
      (define-fun ${s.nameOf(i)} () Int 1)
      (define-fun ${s.nameOf(b)} () Bool (and (= ${s.nameOf(i)} 1) (= 1 ${s.nameOf(i)}) (= true #b1) (= #b0 false) (= 2 2)))""")
    assert(model(b) == And(Seq(Equals(i, IntegerLiteral(1)), Equals(IntegerLiteral(1), i),
      Equals(BooleanLiteral(true), BooleanLiteral(true)), Equals(BooleanLiteral(false), BooleanLiteral(false)),
      Equals(IntegerLiteral(2), IntegerLiteral(2)))))
  }

  test("CVC4 sets") {
    def setOf(text: String): Expr = { val s = cvc4; valueOf(s, set)(s => s"(define-fun ${s.nameOf(set)} () (Set Int) $text)") }
    assertElements(setOf("(as emptyset (Set Int))"), intSet())
    assertElements(setOf("(singleton 1)"), intSet(1))
    assertElements(setOf("(insert 1 2 (singleton 3))"), intSet(1, 2, 3))
    assertElements(setOf("(union (singleton 1) (insert 2 (singleton 1)))"), intSet(1, 2))
  }

  test("CVC4 sets whose type isn't known") {
    val s = cvc4
    assert(modelOf(s, b, set)(s => s"""(define-fun ${s.nameOf(b)} () Bool
      (= (union (singleton 1) (as emptyset (Set Int))) (insert 2 (singleton 1))))""")(b) ==
      Equals(intSet(1), intSet(1, 2)))
  }

  test("CVC4 singletons and insertions whose type isn't known") {
    val s = cvc4
    assert(modelOf(s, b, set)(s => s"""(define-fun ${s.nameOf(b)} () Bool
      (= (singleton 1) (insert 1 (as emptyset (Set Int)))))""")(b) == Equals(intSet(1), intSet(1)))
  }

  test("CVC4 maps given by stores") {
    val s = cvc4
    assertElements(valueOf(s, m)(s => s"""(define-fun ${s.nameOf(m)} () (Array Int Int)
      (store (store ((as const (Array Int Int)) 0) 1 2) 3 4))"""), intMap(1 -> 2, 3 -> 4)(0))
    val t = cvc4
    assertElements(valueOf(t, m)(t => s"""(define-fun ${t.nameOf(m)} () (Array Int Int)
      (store (__array_store_all__ (Array Int Int) 0) 1 2))"""), intMap(1 -> 2)(0))
  }

  test("CVC4 maps whose type isn't known") {
    val s = cvc4
    assert(valueOf(s, b)(s => s"""(define-fun ${s.nameOf(b)} () Bool
      (= (store ((as const (Array Int Int)) 0) 1 2) ((as const (Array Int Int)) 0)))""") ==
      Equals(intMap(1 -> 2)(0), intMap()(0)))
  }
}
