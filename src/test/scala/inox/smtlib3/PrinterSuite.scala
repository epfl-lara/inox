/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package smtlib3

import org.scalatest.funsuite.AnyFunSuite

import java.io.{StringReader, StringWriter}

/** Prints Inox programs in SMT-LIB 3, parses them back, and checks that they mean the same. */
class PrinterSuite extends AnyFunSuite {
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

  private def parseOne(script: String): (InoxProgram, Expr) = {
    val Seq(problem) = Parser(new StringReader(script)).parseScript: @unchecked
    problem
  }

  private def print(program: InoxProgram, expr: Expr): String = {
    val writer = new StringWriter
    val printer = new Printer(program, ctx, writer)
    printer.printScript(expr)
    printer.emit("(check-sat)\n")
    printer.free()
    writer.toString
  }

  /** `script` with the symbols that the printer makes unique (`x!3`) renamed in order of appearance. */
  private def canonical(script: String): String = {
    val names = scala.collection.mutable.Map.empty[String, String]
    """[^\s()|]+(?:![0-9]+)+""".r.replaceAllIn(script, m =>
      scala.util.matching.Regex.quoteReplacement(
        names.getOrElseUpdate(m.matched, m.matched.takeWhile(_ != '!') + "!" + names.size)))
  }

  private def checkWellFormed(program: InoxProgram, expr: Expr, script: String): Unit = {
    import program.symbols.{given, _}
    withClue(script) {
      symbols.ensureWellFormed
      assert(expr.isTyped, s"ill-typed assertion $expr")
    }
  }

  private def reparse(program: InoxProgram, expr: Expr): (InoxProgram, Expr, String) = {
    val script = print(program, expr)
    val (newProgram, newExpr) = try parseOne(script) catch {
      case e: tip.MissformedTIPException => fail(s"couldn't parse the printed script\n$script", e)
    }
    checkWellFormed(newProgram, newExpr, script)
    (newProgram, newExpr, script)
  }

  /** Prints `expr`, parses it back, and checks that printing the result gives the same script.
    *
    * Some Inox trees are printed as combinations of other trees (e.g. the modulo of signed
    * bit-vectors), so only the second printing has to give the same script as the first. */
  private def roundTrip(program: InoxProgram, expr: Expr): (InoxProgram, Expr, String) = {
    val (newProgram, newExpr, script) = reparse(program, expr)
    val (lastProgram, lastExpr, reprinted) = reparse(newProgram, newExpr)
    if (canonical(reprinted) != canonical(script)) {
      val (_, _, last) = reparse(lastProgram, lastExpr)
      assert(canonical(last) == canonical(reprinted), s"printing isn't a fixpoint:\n$reprinted\nbecame\n$last")
    }
    (newProgram, newExpr, script)
  }

  private def status(program: InoxProgram, expr: Expr): String = {
    val res = SimpleSolverAPI(program.getSolver).solveSAT(expr)
    if (res.isSAT) "sat" else if (res.isUNSAT) "unsat" else "unknown"
  }

  /** Round-trips the SMT-LIB 3 `script`, and checks that the result has the expected status. */
  private def scriptTest(name: String, expected: String)(script: String): Unit = test(name) {
    val (program, expr) = parseOne(script)
    checkWellFormed(program, expr, script)
    assert(status(program, expr) == expected, s"unexpected status of\n$script")
    val (newProgram, newExpr, printed) = roundTrip(program, expr)
    assert(status(newProgram, newExpr) == expected, s"unexpected status after printing\n$printed")
  }

  scriptTest("dependent function types", "unsat")(
    """(declare-const isqrt (-> (! Int :var n :restrict (>= n 0))
      |                         (! Int :var r :restrict (and (>= r 0) (<= (* r r) n) (< n (* (+ r 1) (+ r 1)))))))
      |(define-fun twice ((f (-> (! Int :var x :restrict (> x 0)) (! Int :var y :restrict (> y x)))) (z (! Int :var z :restrict (> z 0)))) Int
      |  (f (f z)))
      |(assert (or (= (isqrt 4) 3) (<= (twice (lambda ((x Int)) (+ x 1)) 1) 1)))
      |(check-sat)""".stripMargin)

  scriptTest("dependent results", "unsat")(
    """(define-fun inc ((n (! Int :var n :restrict (>= n 0)))) (! Int :var r :restrict (> r n)) (+ n 1))
      |(assert (<= (inc 2) 2))
      |(check-sat)""".stripMargin)

  scriptTest("dependent tuples", "unsat")(
    """(declare-const p (Tuple (! Int :var n) (! Int :var m :restrict (> m n))))
      |(declare-const q (Tuple Int Bool UnitTuple))
      |(assert (or (<= ((_ tuple.select 1) p) ((_ tuple.select 0) p))
      |            (not (= ((_ tuple.select 2) q) tuple.unit))
      |            (not (= ((_ tuple.select 0) (tuple 1 true tuple.unit)) 1))))
      |(check-sat)""".stripMargin)

  scriptTest("dependent datatype fields", "unsat")(
    """(declare-datatype Interval ((mk (lo Int) (hi (! Int :var h :restrict (<= lo h))))))
      |(declare-const i Interval)
      |(assert (< (hi i) (lo i)))
      |(check-sat)""".stripMargin)

  scriptTest("datatype value parameters", "unsat")(
    """(declare-datatype Vec (par (E (! Int :var n))
      |  ((vnil :restrict (= n 0))
      |   (vcons (head E) (tail (Vec E (- n 1))) :restrict (> n 0)))))
      |(define-fun-rec sum ((v (Vec Int))) Int (match v ((vnil 0) ((vcons h t) (+ h (sum t))))))
      |(declare-const v (Vec Int 2))
      |(assert (or (is-vcons (tail (tail v))) (not (= (sum (vcons 2 1 (vcons 1 2 (as vnil (Vec Int 0))))) 3))))
      |(check-sat)""".stripMargin)

  scriptTest("polymorphic and mutually recursive datatypes", "unsat")(
    """(declare-datatypes ((Tree 1) (Forest 1))
      |  ((par (E) ((node (value E) (children (Forest E)))))
      |   (par (E) ((empty) (grow (first (Tree E)) (rest (Forest E)))))))
      |(define-funs-rec ((size ((t (Tree Int))) Int) (sizes ((f (Forest Int))) Int))
      |  ((+ 1 (sizes (children t)))
      |   (match f ((empty 0) ((grow t r) (+ (size t) (sizes r)))))))
      |(assert (not (= (size (node 1 (grow (node 2 (as empty (Forest Int))) (as empty (Forest Int))))) 2)))
      |(check-sat)""".stripMargin)

  scriptTest("datatype invariants", "unsat")(
    """(declare-datatypes () ((Nat (Z) (S (p Nat)))))
      |(define-fun-rec plus ((x Nat) (y Nat)) Nat (match x (case Z y) (case (S n) (S (plus n y)))))
      |(datatype-invariant n Nat (not (= n (S (S (S Z))))))
      |(declare-const n Nat)
      |(assert (= n (plus (S Z) (S (S Z)))))
      |(check-sat)""".stripMargin)

  scriptTest("custom datatype equality", "unsat")(
    """(declare-datatype Frac ((frac (num Int) (den (! Int :var d :restrict (> d 0))))))
      |(define-fun same ((a Frac) (b Frac)) Bool (= (* (num a) (den b)) (* (num b) (den a))))
      |(datatype-equality Frac same)
      |(declare-const a Frac)
      |(declare-const b Frac)
      |(assert (and (= (num a) 1) (= (den a) 2) (= (num b) 2) (= (den b) 4) (not (= a b))))
      |(check-sat)""".stripMargin)

  scriptTest("unsigned bit-vectors", "unsat")(
    """(declare-const x (! (_ BitVec 8) :unsigned))
      |(declare-const y (_ BitVec 8))
      |(assert (or (bvult x #x00)
      |            (not (= (bvudiv x #x02) (bvlshr x #x01)))
      |            (not (= (bvudiv #xFF #x02) #x7F))
      |            (not (= (bvsdiv #xFF #x02) #x00))
      |            (not (= (bvudiv (! y :unsigned) #x02) (! (bvlshr y #x01) :unsigned)))
      |            (bvslt (! (! #x01 :unsigned) :signed) #x00)
      |            (not (= ((_ zero_extend 8) #xFF) #x00FF))
      |            (not (= ((_ sign_extend 8) #xFF) #xFFFF))
      |            (not (= ((_ extract 7 4) #xA5) #xA))
      |            (not (= (bv2nat #xFF) 255))
      |            (not (= (bvsmod #xF9 #x02) #x01))))
      |(check-sat)""".stripMargin)

  scriptTest("characters", "unsat")(
    """(declare-const c Char)
      |(assert (or (bvult c (! #x0000 :char)) (not (= (! #x0041 :char) (! #x0041 :char)))))
      |(check-sat)""".stripMargin)

  test("ground expressions keep their values") {
    val program = InoxProgram(NoSymbols)
    val evaluator = evaluators.RecursiveEvaluator(program, ctx)

    val s8 = (i: Int) => BVLiteral(true, i, 8)
    val u8 = (i: Int) => BVLiteral(false, i, 8)
    val exprs: Seq[Expr] = Seq(
      // signed and unsigned bit-vector operations
      Division(s8(-7), s8(2)), Division(u8(249), u8(2)),
      Remainder(s8(-7), s8(2)), Remainder(u8(249), u8(2)),
      Modulo(s8(-7), s8(2)), Modulo(s8(7), s8(-2)), Modulo(u8(249), u8(2)),
      LessThan(s8(-1), s8(1)), LessThan(u8(255), u8(1)), GreaterEquals(u8(128), u8(127)),
      Plus(u8(200), u8(100)), Minus(u8(1), u8(2)), Times(s8(-3), s8(5)), UMinus(u8(1)),
      BVAShiftRight(s8(-8), s8(1)), BVLShiftRight(s8(-8), s8(1)), BVShiftLeft(u8(129), u8(1)),
      BVAnd(u8(12), u8(10)), BVOr(s8(12), s8(10)), BVXor(u8(12), u8(10)), BVNot(u8(0)),
      BVWideningCast(s8(-1), BVType(true, 16)), BVWideningCast(u8(255), BVType(false, 16)),
      BVNarrowingCast(BVLiteral(true, -1, 16), BVType(true, 8)),
      BVNarrowingCast(BVLiteral(false, 300, 16), BVType(false, 8)),
      BVSignedToUnsigned(s8(-1)), BVUnsignedToSigned(u8(255)),
      Division(BVSignedToUnsigned(s8(-2)), u8(2)),
      BVToInt(s8(-1)), BVToInt(u8(255)),
      IntToBV(8, true, IntegerLiteral(-1)), IntToBV(8, false, IntegerLiteral(255)),
      // characters, unit and tuples
      CharLiteral('a'), LessThan(CharLiteral('a'), CharLiteral('b')),
      UnitLiteral(), Tuple(Seq(IntegerLiteral(1), UnitLiteral(), u8(3))),
      TupleSelect(Tuple(Seq(IntegerLiteral(1), BooleanLiteral(true))), 2),
      // integers, reals, strings and collections
      Division(IntegerLiteral(-7), IntegerLiteral(2)), Remainder(IntegerLiteral(-7), IntegerLiteral(2)),
      Modulo(IntegerLiteral(-7), IntegerLiteral(2)), Plus(FractionLiteral(1, 2), FractionLiteral(1, 3)),
      StringConcat(StringLiteral("ab"), StringLiteral("c")), StringLength(StringLiteral("abc")),
      SubString(StringLiteral("abcd"), IntegerLiteral(1), IntegerLiteral(3)),
      MapApply(MapUpdated(FiniteMap(Seq.empty, IntegerLiteral(0), IntegerType(), IntegerType()),
        IntegerLiteral(1), IntegerLiteral(2)), IntegerLiteral(1)),
      ElementOfSet(IntegerLiteral(1), SetUnion(FiniteSet(Seq(IntegerLiteral(1)), IntegerType()),
        FiniteSet(Seq(IntegerLiteral(2)), IntegerType()))),
      MultiplicityInBag(IntegerLiteral(1), BagAdd(FiniteBag(Seq(IntegerLiteral(1) -> IntegerLiteral(2)), IntegerType()),
        IntegerLiteral(1))),
      // functions and binders
      locally {
        val x = ValDef.fresh("x", BVType(false, 8))
        Application(Lambda(Seq(x), Plus(x.toVariable, u8(1))), Seq(u8(1)))
      },
    )

    for (e <- exprs) {
      val value = evaluator.eval(e).result.getOrElse(fail(s"couldn't evaluate $e"))
      val (newProgram, newExpr, script) = roundTrip(program, Equals(e, value))
      newExpr match {
        case Equals(l, _) => assert(l.getType(using newProgram.symbols) == e.getType(using program.symbols), script)
        case _ => fail(s"unexpected expression $newExpr for\n$script")
      }
      val result = evaluators.RecursiveEvaluator(newProgram, ctx).eval(newExpr).result
      assert(result == Some(BooleanLiteral(true)), s"$e = $value doesn't hold once printed as\n$script")
    }
  }
}
