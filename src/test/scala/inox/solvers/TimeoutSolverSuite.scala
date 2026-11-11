/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

class TimeoutSolverSuite extends AnyFunSuite {
  import inox.trees.{given, _}
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

  test("Princess stays interrupted until it is reset") {
    val princessCtx = TestContext(Options(Seq(optSelectedSolvers(Set("princess")))))
    val solver = p.getSolver(princessCtx).getNewSolver()

    // Princess doesn't terminate on this query, so the check only returns if the
    // interrupt that arrived before it (e.g. while unrolling) isn't lost.
    val Seq(x, y, z) = Seq("x", "y", "z").map(Variable.fresh(_, IntegerType()))
    solver.assertCnstr(andJoin(Seq(
      x > E(BigInt(0)), y > E(BigInt(0)), z > E(BigInt(0)),
      x * x * x + y * y * y === z * z * z
    )))
    solver.interrupt()

    import scala.concurrent._
    import scala.concurrent.duration._
    import ExecutionContext.Implicits.global
    val res = Await.result(Future(solver.check(SolverResponses.Simple)), 30.seconds)
    assert(res == SolverResponses.Unknown)
    solver.free()
  }
}
