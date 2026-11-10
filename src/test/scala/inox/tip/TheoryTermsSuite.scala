/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package tip

import org.scalatest.funsuite.AnyFunSuite

/** Parses SMT-LIB theory terms and checks that each evaluates to the value the SMT-LIB standard
  * gives it.
  */
class TheoryTermsSuite extends AnyFunSuite {
  import inox.trees._

  /** Parses `(assert term)` and evaluates it, which must give true. */
  private def holds(term: String): Unit = {
    val Seq((program, expr)) = Parser(new java.io.StringReader(s"(assert $term)\n(check-sat)")).parseScript: @unchecked
    val evaluator = program.getEvaluator(TestContext.empty)
    evaluator.eval(expr) match {
      case evaluators.EvaluationResults.Successful(BooleanLiteral(true)) =>
      case got => fail(s"$term parsed as ${expr.asString(using PrinterOptions(symbols = Some(program.symbols)))} gave $got")
    }
  }

  test("Integer and real arithmetic") {
    holds("(= (div 7 2) 3)")
    holds("(= (div (- 7) 2) (- 4))")
    holds("(= (mod (- 7) 2) 1)")
    holds("(= (abs (- 3)) 3)")
    holds("(= (abs 3) 3)")
    holds("(= (/ 1.0 2.0) 0.5)")
    holds("(= (* 2 3) 6)")
    holds("(< 1.5 2.0)")
    holds("(distinct 1 2 3)")
    holds("(not (distinct 1 2 1))")
  }

  test("Bit-vector arithmetic and comparisons") {
    holds("(= (bvadd #x01 #x02) #x03)")
    holds("(= (bvsub #x01 #x02) #xff)")
    holds("(= (bvmul #x03 #x05) #x0f)")
    holds("(= (bvand #x0c #x0a) #x08)")
    holds("(= (bvor #x0c #x0a) #x0e)")
    holds("(= (bvxor #x0c #x0a) #x06)")
    holds("(= (bvsdiv #xf9 #x02) #xfd)")
    holds("(= (bvsrem #xf9 #x02) #xff)")
    holds("(= (bvsmod #xf9 #x02) #x01)")
    holds("(= (bvsmod #x07 #xfe) #xff)")
    holds("(= (bvshl #x01 #x03) #x08)")
    holds("(= (bvashr #x80 #x01) #xc0)")
    holds("(= (bvlshr #x80 #x01) #x40)")
    holds("(bvslt #xff #x01)")
    holds("(bvsle #x01 #x01)")
    holds("(bvsgt #x01 #xff)")
    holds("(bvsge #x01 #x01)")
    holds("(= ((_ sign_extend 8) #xff) #xffff)")
    holds("(= ((_ extract 7 0) #x1234) #x34)")
  }

  test("Unsigned bit-vector operations") {
    holds("(= (bvudiv #xff #x02) #x7f)")
    holds("(= (bvurem #xff #x02) #x01)")
    holds("(bvult #x01 #xff)")
    holds("(bvule #x01 #xff)")
    holds("(bvugt #xff #x01)")
    holds("(bvuge #xff #x01)")
  }

  test("Floating point arithmetic") {
    val one = "(fp #b0 #b01111111 #b00000000000000000000000)"
    val two = "(fp #b0 #b10000000 #b00000000000000000000000)"
    val three = "(fp #b0 #b10000000 #b10000000000000000000000)"
    val half = "(fp #b0 #b01111110 #b00000000000000000000000)"
    val nan = "(_ NaN 8 24)"
    holds(s"(fp.eq (fp.add RNE $one $two) $three)")
    holds(s"(fp.eq (fp.sub RNE $three $two) $one)")
    holds(s"(fp.eq (fp.mul RNE $one $two) $two)")
    holds(s"(fp.eq (fp.div RNE $one $two) $half)")
    holds(s"(fp.eq (fp.fma RNE $one $two $one) $three)")
    holds(s"(fp.eq (fp.neg (fp.neg $one)) $one)")
    holds(s"(fp.eq (fp.abs (fp.neg $one)) $one)")
    holds(s"(fp.eq (fp.max $one $nan) $one)")
    holds(s"(fp.eq (fp.min $nan $two) $two)")
    holds(s"(fp.eq (fp.sqrt RNE (fp.mul RNE $two $two)) $two)")
    holds(s"(fp.eq (fp.roundToIntegral RTP $half) $one)")
    holds(s"(fp.isZero (fp.roundToIntegral RTN $half))")
    holds(s"(fp.isZero (fp.roundToIntegral RTZ $half))")
    holds(s"(fp.eq (fp.roundToIntegral RNA $half) $one)")
    holds(s"(fp.isZero (fp.roundToIntegral RNE $half))")
    holds(s"(fp.lt $one $two)")
    holds(s"(fp.leq $one $one)")
    holds(s"(fp.gt $two $one)")
    holds(s"(fp.geq $two $two)")
    holds(s"(fp.isNaN $nan)")
    holds(s"(fp.isInfinite (_ +oo 8 24))")
    holds(s"(fp.isNegative (_ -zero 8 24))")
    holds(s"(fp.isPositive $one)")
  }

  test("Arrays") {
    holds("(= (select (store ((as const (Array Int Int)) 0) 1 5) 1) 5)")
    holds("(= (select (store ((as const (Array Int Int)) 0) 1 5) 2) 0)")
  }

  test("Binders") {
    holds("(let ((x 1) (y 2)) (= (+ x y) 3))")
    holds("(exists ((x Int)) (= x 1))")
    holds("(! (= 1 1) :named a)")
  }

  test("Conversions between theories") {
    val one = "(fp #b0 #b01111111 #b00000000000000000000000)"
    val minusTwo = "(fp #b1 #b10000000 #b00000000000000000000000)"
    holds("(= (bv2nat #x0f) 15)")
    holds("(= (bv2nat #xff) 255)")
    holds("(= ((_ int2bv 8) 257) #x01)")
    holds("(= ((_ zero_extend 8) #xff) #x00ff)")
    holds("(= ((_ zero_extend 8) #x7f) #x007f)")
    holds("(= (_ bv5 8) #x05)")
    holds(s"(= (bv2nat ((_ fp.to_ubv 8) RNE $one)) 1)")
    holds(s"(= ((_ fp.to_sbv 8) RNE $minusTwo) #xfe)")
    holds(s"(= (fp.to_real $one) 1.0)")
    holds(s"(fp.eq ((_ to_fp 8 24) #x3f800000) $one)")
    holds(s"(fp.eq ((_ to_fp 11 53) RNE $one) ((_ to_fp 11 53) #x3ff0000000000000))")
    holds(s"(fp.isNormal $one)")
    holds("(fp.isSubnormal (fp #b0 #b00000000 #b00000000000000000000001))")
    holds("(= 2.0 (/ 4.0 2.0))")
  }

  test("Declared constants of every sort") {
    def holdsWith(decls: String, term: String): Unit = {
      val Seq((program, expr)) = Parser(new java.io.StringReader(s"$decls\n(assert $term)\n(check-sat)")).parseScript: @unchecked
      assert(expr.getType(using program.symbols) == BooleanType(), s"for $term")
    }
    holdsWith("(declare-const f (_ FloatingPoint 8 24))", "(fp.isZero f)")
    holdsWith("(declare-const r RoundingMode)", "(= r RNE)")
    holdsWith("(declare-const a (Array Int Int))", "(= (select (store a 1 2) 1) 2)")
    holdsWith("(declare-const a (Array Int Int)) (declare-const k Int)", "(= (select a k) (select a (+ k 0)))")
  }
}
