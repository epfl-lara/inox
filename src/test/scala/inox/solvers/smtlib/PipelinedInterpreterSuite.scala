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
class PipelinedInterpreterSuite extends AnyFunSuite {

  private val cvcArgs = Array("-q", "--incremental", "--print-success", "--lang", "smt2.6")

  private val solvers: Seq[(String, () => Boolean, () => PipelinedInterpreter)] = Seq(
    ("z3", () => SolverFactory.hasZ3,
      () => new PipelinedZ3Interpreter("z3", Array("-in", "-smt2"), out => new Parser(new Lexer(out)))),
    ("cvc4", () => SolverFactory.hasCVC4, () => new PipelinedCVC4Interpreter("cvc4", cvcArgs)),
    ("cvc5", () => SolverFactory.hasCVC5, () => new PipelinedCVC5Interpreter("cvc5", cvcArgs)),
    ("bitwuzla", () => SolverFactory.hasBitwuzla,
      () => new PipelinedBitwuzlaInterpreter("bitwuzla", Array("-v", "0", "--produce-models", "--lang", "smt2"))),
  )

  private val b = SSymbol("b")
  private val bRef = QualifiedIdentifier(SimpleIdentifier(b))

  for ((name, available, create) <- solvers) {
    def withSolver(body: PipelinedInterpreter => Unit): Unit = {
      assume(available(), s"$name isn't available")
      val solver = create()
      try {
        assert(solver.eval(SetLogic(ALL())) == Success)
        body(solver)
      } finally solver.free()
    }

    test(s"$name: Sent commands are answered before the next evaluated one") {
      withSolver { solver =>
        assert(solver.pipelines(DeclareConst(b, BoolSort())))
        solver.send(DeclareConst(b, BoolSort()))
        solver.send(Assert(Not(bRef)))
        assert(solver.eval(CheckSat()) == CheckSatStatus(SatStatus))
        solver.send(Assert(bRef))
        assert(solver.eval(CheckSat()) == CheckSatStatus(UnsatStatus))
        assert(solver.pendingError().isEmpty)
      }
    }

    test(s"$name: Many sent commands don't fill the pipes") {
      withSolver { solver =>
        // well beyond the 8192 `success` answers that fill a 64 KiB pipe of Linux
        for (i <- 0 until 20000) solver.send(DeclareConst(SSymbol(s"c$i"), BoolSort()))
        assert(solver.eval(CheckSat()) == CheckSatStatus(SatStatus))
        assert(solver.pendingError().isEmpty)
      }
    }

    test(s"$name: The error of a sent command is reported once") {
      withSolver { solver =>
        solver.send(Assert(bRef)) // b isn't declared
        solver.eval(CheckSat()) // some solvers exit on the error, so that the answer is unspecified
        assert(solver.pendingError().nonEmpty)
        assert(solver.pendingError().isEmpty)
      }
    }
  }

  test("z3: Many errors of sent commands don't fill the pipes") {
    val (_, available, create) = solvers.head
    assume(available(), "z3 isn't available")
    val solver = create()
    try {
      // z3 goes on after an error, and answers each of these with a message of about 70 characters
      for (_ <- 0 until 20000) solver.send(Assert(bRef)) // b isn't declared
      assert(solver.eval(CheckSat()) == CheckSatStatus(SatStatus))
      assert(solver.pendingError().nonEmpty)
    } finally solver.free()
  }

  test("z3: The error of a sent command is forgotten by a reset") {
    val (_, available, create) = solvers.head
    assume(available(), "z3 isn't available")
    val solver = create()
    try {
      solver.send(Assert(bRef)) // b isn't declared
      assert(solver.eval(Reset()) == Success)
      assert(solver.pendingError().isEmpty)
      assert(solver.eval(CheckSat()) == CheckSatStatus(SatStatus))
    } finally solver.free()
  }

  test("z3: A reset that isn't waited for forgets the declarations, and is ready when awaited") {
    assume(SolverFactory.hasZ3, "z3 isn't available")
    val z3 = new PipelinedZ3Interpreter("z3", Array("-in", "-smt2"), out => new Parser(new Lexer(out)))
    try {
      z3.send(DeclareConst(b, BoolSort()))
      z3.send(Assert(Not(bRef)))
      assert(z3.eval(CheckSat()) == CheckSatStatus(SatStatus))
      z3.send(Assert(QualifiedIdentifier(SimpleIdentifier(SSymbol("c"))))) // c isn't declared
      z3.resetLater()
      assert(z3.awaitReset())

      z3.send(Assert(bRef)) // b isn't declared anymore
      assert(z3.eval(CheckSat()) == CheckSatStatus(SatStatus))
      assert(z3.pendingError().nonEmpty)
    } finally z3.free()
  }

  test("z3: A reset that isn't waited for forgets the commands sent before it, unanswered") {
    assume(SolverFactory.hasZ3, "z3 isn't available")
    val z3 = new PipelinedZ3Interpreter("z3", Array("-in", "-smt2"), out => new Parser(new Lexer(out)))
    try {
      z3.send(DeclareConst(b, BoolSort())) // not answered before the reset
      z3.resetLater()
      assert(z3.awaitReset())
      z3.send(Assert(bRef)) // b isn't declared anymore
      assert(z3.eval(CheckSat()) == CheckSatStatus(SatStatus))
      assert(z3.pendingError().nonEmpty)
    } finally z3.free()
  }

  test("z3: A reset that isn't waited for fails once the process is gone") {
    assume(SolverFactory.hasZ3, "z3 isn't available")
    val z3 = new PipelinedZ3Interpreter("z3", Array("-in", "-smt2"), out => new Parser(new Lexer(out)))
    try {
      z3.resetLater()
      z3.kill()
      assert(!z3.awaitReset())
    } finally z3.free()
  }
}
