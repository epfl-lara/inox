/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

import inox.solvers.combinators._

class SolverPoolSuite extends AnyFunSuite {
  import inox.trees._
  import SolverResponses._

  given ctx: Context = TestContext.empty
  val p = InoxProgram(NoSymbols)
  val sfactory: SolverFactory { val program: InoxProgram } =
    SolverFactory.create(p)("dummy", () => new DummySolver(p).asInstanceOf)

  private class DummySolver(override val program: InoxProgram,
                            override val context: Context) extends Solver {

    def this(program: InoxProgram) = this(program, ctx)

    val name = "Dummy"
    val description = "dummy"

    def declare(vd: ValDef) = ()
    def assertCnstr(e: Expr) = ()
    def check(config: CheckConfiguration): config.Response[Model, Assumptions] = config.cast(Unknown)
    def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = config.cast(Unknown)
    def free() = ()
    def reset() = ()
    def push() = ()
    def pop() = ()
    def interrupt() = ()
  }

  val poolSize = 5

  test(s"SolverPool has at least $poolSize solvers") {

    val sp = SolverPoolFactory(sfactory)

    var solvers = Set[Solver]()

    for (i <- 1 to poolSize) {
      solvers += sp.getNewSolver()
    }

    solvers.size === poolSize
  }

  test("SolverPool reuses solvers") {

    val sp = SolverPoolFactory(sfactory)

    var solvers = Set[Solver]()

    for (i <- 1 to poolSize) {
      val s = sp.getNewSolver()
      solvers += s
      sp.reclaim(s)
    }

    for (i <- 1 to poolSize) {
      val s = sp.getNewSolver()
      assert(solvers contains s, "Solver not reused?")
      sp.reclaim(s)
    }
  }

  test(s"SolverPool can grow") {

    val sp = SolverPoolFactory(sfactory)

    var solvers = Set[Solver]()

    for (i <- 1 to poolSize+3) {
      solvers += sp.getNewSolver()
    }

    solvers.size === poolSize+3
  }
}
