/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package combinators

import org.scalatest.funsuite.AnyFunSuite

import scala.concurrent.duration._

/** Runs a portfolio of scripted solvers and the `eval` solver, so that the outcome
  * of each check is known in advance.
  */
class PortfolioSolverSuite extends AnyFunSuite {
  import inox.trees._
  import SolverResponses._

  val program = InoxProgram(NoSymbols)
  val ctx = TestContext.empty

  /** Always answers `answer` and records the calls it receives. */
  class ScriptedSolver(override val program: PortfolioSolverSuite.this.program.type, override val context: Context, val name: String, answer: => SolverResponse[Nothing, Nothing])
    extends Solver {
    val calls = scala.collection.mutable.ListBuffer.empty[String]
    @volatile var interrupted = false

    private def respond(config: Configuration): config.Response[Model, Assumptions] = synchronized {
      calls += "check"
      config.cast(answer)
    }

    def declare(vd: ValDef) = synchronized { calls += s"declare ${vd.id}" }
    def assertCnstr(e: Expr) = synchronized { calls += s"assert $e" }
    def check(config: CheckConfiguration): config.Response[Model, Assumptions] = respond(config)
    def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
      synchronized { calls += s"assume ${assumptions.mkString(",")}" }
      respond(config)
    }
    def free() = synchronized { calls += "free" }
    def reset() = synchronized { calls += "reset" }
    def push() = synchronized { calls += "push" }
    def pop() = synchronized { calls += "pop" }
    def interrupt() = { interrupted = true }
  }

  def scripted(name: String, answer: => SolverResponse[Nothing, Nothing]) = {
    val solver = new ScriptedSolver(program, ctx, name, answer) with TimeoutSolver
    val factory = SolverFactory.create[ScriptedSolver & TimeoutSolver](program)(name, () => solver)
    (solver, factory)
  }

  val evalFactory = SolverFactory("eval", program, ctx, force = true)

  val x = Variable.fresh("x", BooleanType())

  test("The factory is named after its solvers") {
    val (_, a) = scripted("a", Unknown)
    val (_, b) = scripted("b", Unknown)
    assert(PortfolioSolverFactory(program)(Seq(a, b)).name == "Pfolio(a,b)")
  }

  test("The first known answer wins and names the solver that found it") {
    val (unknown, uf) = scripted("unknown", Unknown)
    val (sat, sf) = scripted("sat", Sat)
    val factory = PortfolioSolverFactory(program)(Seq(uf, sf))
    val s = factory.getNewSolver()
    assert(s.name == "Pfolio")
    assert(s.getResultSolver.isEmpty)
    s.assertCnstr(x)
    assert(s.check(Simple) == Sat)
    assert(s.getResultSolver == Some(sat))
    assert(unknown.interrupted && sat.interrupted)
  }

  test("Unknown when no solver knows the answer") {
    val (_, a) = scripted("a", Unknown)
    val (_, b) = scripted("b", Unknown)
    val s = PortfolioSolverFactory(program)(Seq(a, b)).getNewSolver()
    assert(s.check(Model) == Unknown)
  }

  test("The evaluator answers ground constraints in a portfolio") {
    val (_, uf) = scripted("unknown", Unknown)
    val factory = PortfolioSolverFactory(program)(Seq(uf, evalFactory))
    val api = SimpleSolverAPI(factory)
    assert(api.solveVALID(BooleanLiteral(true)) == Some(true))
    assert(api.solveVALID(BooleanLiteral(false)) == Some(false))
    assert(api.solveVALID(Or(x, Not(x))) == None)
  }

  test("Every call is forwarded to every solver in order") {
    val (a, af) = scripted("a", Unknown)
    val (b, bf) = scripted("b", Unsat)
    val factory = PortfolioSolverFactory(program)(Seq(af, bf))
    val s = factory.getNewSolver()
    s.declare(x.toVal)
    s.push()
    s.assertCnstr(x)
    s.pop()
    s.reset()
    assert(s.checkAssumptions(Simple)(Set(Not(x))) == Unsat)
    assert(s.getResultSolver == Some(b))
    factory.reclaim(s)
    s.check(Simple) // waits for the reclaim to run

    val expected = Seq(s"declare ${x.id}", "push", s"assert $x", "pop", "reset", s"assume ${Not(x)}", "check", "free", "check")
    assert(a.calls.toSeq == expected)
    assert(b.calls.toSeq == expected)
  }

  test("Unsatisfiable cores come from the solver that answered") {
    val (_, a) = scripted("a", UnsatWithAssumptions(Set(x)).asInstanceOf[SolverResponse[Nothing, Nothing]])
    val s = PortfolioSolverFactory(program)(Seq(a)).getNewSolver()
    assert(s.checkAssumptions(UnsatAssumptions)(Set(x)) == UnsatWithAssumptions(Set(x)))
  }

  test("SMT-LIB file ids come from the first solver") {
    val (_, a) = scripted("a", Unknown)
    assert(PortfolioSolverFactory(program)(Seq(a)).getNewSolver().getSmtLibFileId.isEmpty)
    class Empty(override val program: PortfolioSolverSuite.this.program.type, override val context: Context)
      extends PortfolioSolver with TimeoutSolver { val solvers = Seq() }
    val empty = new Empty(program, ctx)
    assert(empty.getSmtLibFileId.isEmpty)
    assert(empty.check(Simple) == Unknown)
  }

  test("Debug messages, interrupts and frees reach every solver") {
    var debugged = Seq.empty[String]
    class Debugged(name: String) extends ScriptedSolver(program, ctx, name, Unknown) {
      override def dbg(msg: => Any): Unit = synchronized { debugged :+= s"$name: $msg" }
    }
    val a = new Debugged("a") with TimeoutSolver
    val b = new Debugged("b") with TimeoutSolver
    val factory = PortfolioSolverFactory(program)(Seq(
      SolverFactory.create[Debugged & TimeoutSolver](program)("a", () => a),
      SolverFactory.create[Debugged & TimeoutSolver](program)("b", () => b)))
    val s = factory.getNewSolver()
    s.dbg("hello")
    assert(debugged.sorted == Seq("a: hello", "b: hello"))
    s.interrupt()
    assert(a.interrupted && b.interrupted)
    s.free()
    s.check(Simple) // waits for the free to run
    assert(a.calls.contains("free") && b.calls.contains("free"))
  }

  test("A solver that doesn't stop after the interrupt is a fatal error that shows its stack") {
    val stopped = new java.util.concurrent.CountDownLatch(1)
    val (slow, _) = scripted("slow", { stopped.await(); Unknown })
    val (sat, _) = scripted("sat", Sat)
    class Impatient(override val program: PortfolioSolverSuite.this.program.type, override val context: Context)
      extends PortfolioSolver with TimeoutSolver {
      val solvers = Seq(slow, sat)
      override val stopTimeout = 200.millis
    }
    try {
      val error = intercept[FatalError](new Impatient(program, ctx).check(Simple))
      assert(error.msg.contains("Solver slow in portfolio did not stop within 200 milliseconds"))
      assert(error.msg.contains("CountDownLatch.await"), error.msg)
      assert(slow.interrupted && sat.interrupted)
    } finally {
      stopped.countDown()
    }
  }

  test("A solver that overflows the stack counts as unknown") {
    val (_, overflow) = scripted("overflow", throw new StackOverflowError)
    val (sat, sf) = scripted("sat", Sat)
    val s = PortfolioSolverFactory(program)(Seq(overflow, sf)).getNewSolver()
    assert(s.check(Simple) == Sat)
    assert(s.getResultSolver == Some(sat))

    val alone = PortfolioSolverFactory(program)(Seq(overflow)).getNewSolver()
    assert(alone.check(Simple) == Unknown)
  }
}
