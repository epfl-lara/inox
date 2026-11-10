/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import org.scalatest.funsuite.AnyFunSuite

import _root_.smtlib.parser.Parser

import _root_.smtlib.lexer.Lexer
import _root_.smtlib.trees.Terms._
import _root_.smtlib.trees.Commands._
import _root_.smtlib.trees.CommandsResponses._
import _root_.smtlib.theories.Core._

/** The commands sent without waiting for their answers, and the errors they answer. */
class PipelinedZ3InterpreterSuite extends AnyFunSuite {

  private def withZ3(body: PipelinedZ3Interpreter => Unit): Unit = {
    assume(SolverFactory.hasZ3, "z3 isn't available")
    val z3 = new PipelinedZ3Interpreter("z3", Array("-in", "-smt2"), out => new Parser(new Lexer(out)))
    try body(z3) finally z3.free()
  }

  private val b = SSymbol("b")
  private val bRef = QualifiedIdentifier(SimpleIdentifier(b))

  test("Sent commands are answered before the next evaluated one") {
    withZ3 { z3 =>
      assert(z3.pipelines(DeclareConst(b, BoolSort())))
      z3.send(DeclareConst(b, BoolSort()))
      z3.send(Assert(Not(bRef)))
      assert(z3.eval(CheckSat()) == CheckSatStatus(SatStatus))
      z3.send(Assert(bRef))
      assert(z3.eval(CheckSat()) == CheckSatStatus(UnsatStatus))
      assert(z3.pendingError().isEmpty)
    }
  }

  test("The error of a sent command is reported once, and forgotten by a reset") {
    withZ3 { z3 =>
      z3.send(Assert(bRef)) // b isn't declared
      assert(z3.eval(CheckSat()) == CheckSatStatus(SatStatus))
      assert(z3.pendingError().nonEmpty)
      assert(z3.pendingError().isEmpty)

      z3.send(Assert(bRef))
      assert(z3.eval(Reset()) == Success)
      assert(z3.pendingError().isEmpty)
    }
  }
}
