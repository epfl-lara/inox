/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package evaluators

import org.scalatest.funsuite.AnyFunSuite

/** Semantics of the recursive evaluator that follow SMT-LIB where the evaluators of other projects, tested
  * through [[EvaluatorSuite]], differ: Stainless's evaluators take the amount of `Int32` and `Int64` shifts
  * modulo the width, as the JVM does, and its code generator shifts unsigned bitvectors logically.
  */
class RecursiveEvaluatorSuite extends AnyFunSuite {
  import inox.trees._

  val ctx = TestContext.empty
  val program = InoxProgram(NoSymbols)
  val evaluator = RecursiveEvaluator(program, ctx)

  def eval(expr: Expr): Expr = evaluator.eval(expr) match {
    case EvaluationResults.Successful(res) => res
    case other => fail(s"Evaluation of '$expr' failed with $other")
  }

  test("Int32 and Int64 shifts by out-of-range amounts") {
    // The amount is read as an unsigned value: shifting by the width or more, or by a negative amount, vacates
    // all the bits, which `>>` fills with the most significant bit
    assert(eval(BVShiftLeft(Int32Literal(1), Int32Literal(32)))                     === Int32Literal(0))
    assert(eval(BVShiftLeft(Int32Literal(1), Int32Literal(33)))                     === Int32Literal(0))
    assert(eval(BVShiftLeft(Int32Literal(1), Int32Literal(-1)))                     === Int32Literal(0))
    assert(eval(BVShiftLeft(Int32Literal(Int.MinValue), Int32Literal(-1)))          === Int32Literal(0))
    assert(eval(BVLShiftRight(Int32Literal(Int.MinValue), Int32Literal(32)))        === Int32Literal(0))
    assert(eval(BVLShiftRight(Int32Literal(Int.MinValue), Int32Literal(33)))        === Int32Literal(0))
    assert(eval(BVLShiftRight(Int32Literal(-1), Int32Literal(-1)))                  === Int32Literal(0))
    assert(eval(BVAShiftRight(Int32Literal(Int.MinValue), Int32Literal(32)))        === Int32Literal(-1))
    assert(eval(BVAShiftRight(Int32Literal(Int.MinValue), Int32Literal(33)))        === Int32Literal(-1))
    assert(eval(BVAShiftRight(Int32Literal(Int.MinValue), Int32Literal(-1)))        === Int32Literal(-1))
    assert(eval(BVAShiftRight(Int32Literal(Int.MaxValue), Int32Literal(32)))        === Int32Literal(0))
    assert(eval(BVAShiftRight(Int32Literal(Int.MaxValue), Int32Literal(-1)))        === Int32Literal(0))

    assert(eval(BVShiftLeft(Int64Literal(1), Int64Literal(64)))                     === Int64Literal(0))
    assert(eval(BVShiftLeft(Int64Literal(1), Int64Literal(65)))                     === Int64Literal(0))
    assert(eval(BVShiftLeft(Int64Literal(1), Int64Literal(1L << 32)))               === Int64Literal(0))
    assert(eval(BVShiftLeft(Int64Literal(1), Int64Literal(-1)))                     === Int64Literal(0))
    assert(eval(BVLShiftRight(Int64Literal(-1), Int64Literal(64)))                  === Int64Literal(0))
    assert(eval(BVAShiftRight(Int64Literal(Long.MinValue), Int64Literal(64)))       === Int64Literal(-1))
    assert(eval(BVAShiftRight(Int64Literal(Long.MinValue), Int64Literal(1L << 32))) === Int64Literal(-1))
  }

  test("`>>` on unsigned bitvectors fills with the most significant bit, as SMT-LIB `bvashr`") {
    def ubvl(x: BigInt) = BVLiteral(false, x, 11)
    assert(eval(BVAShiftRight(ubvl(1024), ubvl(1)))  === ubvl(1536))
    assert(eval(BVAShiftRight(ubvl(1024), ubvl(11))) === ubvl(2047))
    assert(eval(BVAShiftRight(ubvl(1023), ubvl(11))) === ubvl(0))
  }
}
