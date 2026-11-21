/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

import scala.concurrent.duration._

/** Checks that the solvers that have a resource limit (`--z3-rlimit`, `--cvc5-rlimit`) record what
  * each of their checks spent (`resourceUsage`), in the units of that limit.
  */
class ResourceUsageSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses._

  private val program = InoxProgram(NoSymbols)
  private given Symbols = program.symbols

  private val Seq(x, y, z) = Seq("x", "y", "z").map(Variable.fresh(_, IntegerType()))

  // Satisfiable only by a counterexample to Fermat's last theorem for n = 3: the solvers can't
  // decide it, so they run until they are stopped by their resource limit or a timeout.
  private val hard = andJoin(Seq(
    x > E(BigInt(0)), y > E(BigInt(0)), z > E(BigInt(0)),
    x * x * x + y * y * y === z * z * z
  ))

  private case class SmtSolver(name: String, available: () => Boolean, rlimit: IntOptionDef)

  private def requireSolver(name: String, available: Boolean): Unit =
    if (SolverTestSuite.requiredSolvers(name)) assert(available, s"Solver $name is required but isn't available")
    else assume(available, s"$name is not available")

  private val smtSolvers = Seq(
    SmtSolver("smt-z3", () => SolverFactory.hasZ3, smtlib.optZ3Rlimit),
    SmtSolver("nativez3", () => SolverFactory.hasNativeZ3, smtlib.optZ3Rlimit),
    SmtSolver("unrollz3", () => SolverFactory.hasNativeZ3, smtlib.optZ3Rlimit),
    SmtSolver("smt-cvc5", () => SolverFactory.hasCVC5, smtlib.optCVC5Rlimit)
  )

  private val million = 1000000L

  /** Runs `body` on a fresh solver. The timeout keeps a failing test from hanging. */
  private def withSolver[T](solver: String, options: OptionValue[?]*)(body: Solver { val program: InoxProgram } => T): T = {
    val ctx = TestContext(Options(optSelectedSolvers(Set(solver)) +: options))
    val factory = program.getSolver(ctx).withTimeout(60.seconds)
    val s = factory.getNewSolver()
    try body(s) finally factory.reclaim(s)
  }

  for (solver <- smtSolvers) {
    test(s"${solver.name}: nothing is recorded before the first check") {
      requireSolver(solver.name, solver.available())
      withSolver(solver.name) { s =>
        s.assertCnstr(x > E(BigInt(0)))
        assert(s.resourceUsage == ResourceUsage.empty)
        assert(s.resourceUsage.usage.isEmpty)
      }
    }

    test(s"${solver.name}: each check records what it spent") {
      requireSolver(solver.name, solver.available())
      withSolver(solver.name) { s =>
        s.assertCnstr(x > E(BigInt(0)))
        assert(s.check(Simple) == Sat)
        val first = s.resourceUsage.perCheck
        assert(first.nonEmpty && first.forall(_ >= 0) && first.sum > 0)

        s.assertCnstr(x * x === E(BigInt(49)))
        assert(s.check(Simple) == Sat)
        val both = s.resourceUsage.perCheck
        assert(both.size > first.size && both.startsWith(first))
        assert(both.forall(_ >= 0) && both.drop(first.size).sum > 0)
        assert(s.resourceUsage.usage.contains(both.max))
      }
    }

    test(s"${solver.name}: a check stopped by the resource limit spent that limit") {
      requireSolver(solver.name, solver.available())
      withSolver(solver.name, solver.rlimit(1)) { s =>
        s.assertCnstr(hard)
        assert(s.check(Simple) == Unknown)
        assert(s.resourceLimitReached)
        val spent = s.resourceUsage.usage.get
        // cvc5 only notices that it is over its limit after a few more units
        assert(spent >= million && spent <= million + million / 10)
      }
    }

    test(s"${solver.name}: a check that spent less than the limit answers under that limit") {
      requireSolver(solver.name, solver.available())
      val formula = andJoin(Seq(x > E(BigInt(3)), y > x, x * y === E(BigInt(221))))
      val spent = withSolver(solver.name) { s =>
        s.assertCnstr(formula)
        assert(s.check(Simple) == Sat)
        s.resourceUsage.usage.get
      }
      assert(spent < million)
      withSolver(solver.name, solver.rlimit(1)) { s =>
        s.assertCnstr(formula)
        assert(s.check(Simple) == Sat)
        assert(s.resourceUsage.usage.contains(spent))
      }
    }
  }

  test("no-inc:smt-z3: the solvers of all the checks are counted, although they were freed") {
    requireSolver("smt-z3", SolverFactory.hasZ3)
    withSolver("no-inc:smt-z3") { s =>
      s.assertCnstr(x > E(BigInt(0)))
      assert(s.check(Simple) == Sat)
      val first = s.resourceUsage.perCheck
      assert(first.nonEmpty)
      assert(s.check(Simple) == Sat)
      assert(s.resourceUsage.perCheck.size == 2 * first.size)
    }
  }

  test("a portfolio reports the resources of the solver that answered, if any") {
    requireSolver("smt-z3", SolverFactory.hasZ3)
    requireSolver("smt-cvc5", SolverFactory.hasCVC5)
    val solvers = optSelectedSolvers(Set("smt-z3", "smt-cvc5"))
    val factory = program.getSolver(TestContext(Options(Seq(solvers)))).withTimeout(60.seconds)
    val s = factory.getNewSolver()
    try {
      s.assertCnstr(x > E(BigInt(0)))
      assert(s.check(Simple) == Sat)
      assert(s.resourceUsage.perCheck.nonEmpty)
    } finally factory.reclaim(s)

    val limited = Options(Seq(solvers, smtlib.optZ3Rlimit(1), smtlib.optCVC5Rlimit(1)))
    val limitedFactory = program.getSolver(TestContext(limited)).withTimeout(60.seconds)
    val t = limitedFactory.getNewSolver()
    try {
      t.assertCnstr(hard)
      assert(t.check(Simple) == Unknown)
      assert(t.resourceUsage == ResourceUsage.empty)
    } finally limitedFactory.reclaim(t)
  }
}
