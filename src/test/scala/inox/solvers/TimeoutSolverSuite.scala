/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

class TimeoutSolverSuite extends AnyFunSuite {
  import inox.trees._
  import dsl._

  val ctx = TestContext.empty
  val p = InoxProgram(NoSymbols)

  private class IdioticSolver(override val program: p.type,
                              override val context: Context) extends Solver {
    def this() = this(p, ctx)

    val name = "Idiotic"

    var interrupted = false

    import SolverResponses._
    override def check(config: CheckConfiguration): config.Response[Model, Assumptions] = {
      while(!interrupted) Thread.sleep(50L)
      config.cast(Unknown)
    }

    override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
      while(!interrupted) Thread.sleep(50L)
      config.cast(Unknown)
    }

    def interrupt(): Unit = { interrupted = true }

    def declare(vd: ValDef) = ()
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

    val x = Variable.fresh("x", IntegerType())
    assert(SimpleSolverAPI(sfactory).solveVALID(x === x) === None)
  }

  test("TimeoutSolver 2") {
    val x = Variable.fresh("x", IntegerType())
    assert(SimpleSolverAPI(sfactory).solveVALID(x + E(BigInt(1)) === E(BigInt(1)) + x) === None)
    assert(SimpleSolverAPI(sfactory).solveVALID(x + E(BigInt(1)) === x) === None)
  }
}
