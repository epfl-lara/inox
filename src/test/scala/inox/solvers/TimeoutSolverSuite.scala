/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import org.scalatest._

class TimeoutSolverSuite extends FunSuite {
  import inox.trees._
  import dsl._

  val ctx = TestContext.empty
  val p = InoxProgram(ctx, NoSymbols)

  private class IdioticSolver extends Solver {
    val name = "Idiotic"
    val program: p.type = p
    val options = ctx.options

    var interrupted = false

    import SolverResponses._
    def check(config: CheckConfiguration): config.Response[Model, Assumptions] = {
      while(!interrupted) Thread.sleep(50L)
      config.cast(Unknown)
    }

    def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
      while(!interrupted) Thread.sleep(50L)
      config.cast(Unknown)
    }

    def interrupt(): Unit = { interrupted = true }

    def assertCnstr(e: Expr) = ()

    def push(): Unit = ()
    def pop(): Unit = ()
    def free(): Unit = ()
    def reset(): Unit = ()
  }

  private val sfactory = SolverFactory.create(p)("idiotic",
    () => (new IdioticSolver with combinators.TimeoutSolver).setTimeout(200L))

  test("TimeoutSolver 1") {
    assert(SimpleSolverAPI(sfactory).solveVALID(BooleanLiteral(true)) === None)
    assert(SimpleSolverAPI(sfactory).solveVALID(BooleanLiteral(false)) === None)

    val x = Variable.fresh("x", IntegerType)
    assert(SimpleSolverAPI(sfactory).solveVALID(x === x) === None)
  }

  test("TimeoutSolver 2") {
    val x = Variable.fresh("x", IntegerType)
    assert(SimpleSolverAPI(sfactory).solveVALID(x + E(BigInt(1)) === E(BigInt(1)) + x) === None)
    assert(SimpleSolverAPI(sfactory).solveVALID(x + E(BigInt(1)) === x) === None)
  }
}
