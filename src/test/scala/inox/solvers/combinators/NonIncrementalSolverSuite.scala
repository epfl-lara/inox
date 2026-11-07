/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package combinators

import org.scalatest.funsuite.AnyFunSuite

class NonIncrementalSolverSuite extends AnyFunSuite {
  import inox.trees._
  import SolverResponses._

  val p = InoxProgram(NoSymbols)
  val ctx = TestContext.empty

  /** Throws on its first check and answers `Unknown` on the next ones. */
  class FlakySolver(override val program: p.type, override val context: Context, log: scala.collection.mutable.ListBuffer[String])
    extends Solver {
    val name = "flaky"
    private def respond(config: Configuration): config.Response[Model, Assumptions] = {
      log += "check"
      if (log.count(_ == "check") == 1) throw new IllegalStateException("first check")
      config.cast(Unknown)
    }
    def declare(vd: ValDef) = ()
    def assertCnstr(e: Expr) = ()
    def check(config: CheckConfiguration): config.Response[Model, Assumptions] = respond(config)
    def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = respond(config)
    def free() = log += "free"
    def reset() = ()
    def push() = ()
    def pop() = ()
    def interrupt() = ()
  }

  def nonIncremental(log: scala.collection.mutable.ListBuffer[String]) = new NonIncrementalSolver {
    val program: p.type = p
    val context = ctx
    type Trees = Expr
    type Model = inox.Model { val program: p.type }
    def name = "no-inc:flaky"
    def underlying() = new FlakySolver(p, ctx, log).asInstanceOf[AbstractSolver {
      val program: p.type
      type Trees = Expr
      type Model = inox.Model { val program: p.type }
    }]
  }

  test("A check that throws leaves the solver usable") {
    val log = scala.collection.mutable.ListBuffer.empty[String]
    val solver = nonIncremental(log)
    intercept[IllegalStateException](solver.check(Simple))
    assert(solver.currentSolver.isEmpty)
    assert(solver.check(Simple) == Unknown)
    solver.free()
    assert(log.toList == List("check", "free", "check", "free"))
  }

  test("A check with assumptions that throws leaves the solver usable") {
    val log = scala.collection.mutable.ListBuffer.empty[String]
    val solver = nonIncremental(log)
    intercept[IllegalStateException](solver.checkAssumptions(Simple)(Set.empty))
    assert(solver.currentSolver.isEmpty)
    assert(solver.checkAssumptions(Simple)(Set.empty) == Unknown)
    solver.free()
    assert(log.toList == List("check", "free", "check", "free"))
  }
}
