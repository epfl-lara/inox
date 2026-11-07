/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import org.scalatest.funsuite.AnyFunSuite

import _root_.smtlib.printer.RecursivePrinter
import _root_.smtlib.trees.Terms._
import _root_.smtlib.trees.SimpleTreeTransformer
import _root_.smtlib.theories.Ints._
import optimization.Commands._

/** Parsing, printing and transforming the optimization commands of Z3. */
class OptimizationCommandsSuite extends AnyFunSuite {

  def parse(s: String) = {
    val parser = new optimization.Parser(new optimization.Lexer(new java.io.StringReader(s)))
    parser.parseCommand
  }

  val x = QualifiedIdentifier(SimpleIdentifier(SSymbol("x")))
  val y = QualifiedIdentifier(SimpleIdentifier(SSymbol("y")))

  val commands = Seq(
    "(maximize x)" -> Maximize(x),
    "(minimize (+ x 1))" -> Minimize(Add(x, NumeralLit(1))),
    "(assert-soft (> x 0))" -> AssertSoft(GreaterThan(x, NumeralLit(0)), None, None),
    "(assert-soft (> x 0) :weight 3)" -> AssertSoft(GreaterThan(x, NumeralLit(0)), Some(3), None),
    "(assert-soft (> x 0) :id goal)" -> AssertSoft(GreaterThan(x, NumeralLit(0)), None, Some("goal")),
    "(assert-soft (> x 0) :weight 3 :id goal)" -> AssertSoft(GreaterThan(x, NumeralLit(0)), Some(3), Some("goal"))
  )

  test("Parsing optimization commands") {
    for ((s, cmd) <- commands) assert(parse(s) == cmd, s)
  }

  test("Printing optimization commands") {
    for ((s, cmd) <- commands) {
      assert(RecursivePrinter.toString(cmd).trim == s)
      assert(parse(RecursivePrinter.toString(cmd)) == cmd)
    }
  }

  test("Other commands still parse") {
    assert(parse("(check-sat)") == _root_.smtlib.trees.Commands.CheckSat())
  }

  test("Transforming optimization commands") {
    val rename = new SimpleTreeTransformer {
      def pre(term: Term): Term = term
      def post(term: Term): Term = if (term == x) y else term
      def pre(sort: Sort): Sort = sort
      def post(sort: Sort): Sort = sort
    }
    assert(rename.transform(Maximize(x), ())._1 == Maximize(y))
    assert(rename.transform(Minimize(Add(x, x)), ())._1 == Minimize(Add(y, y)))
    assert(rename.transform(AssertSoft(x, Some(2), Some("g")), ())._1 == AssertSoft(y, Some(2), Some("g")))
  }
}
