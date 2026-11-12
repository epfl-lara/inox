/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

import scala.concurrent.duration._

/** Checks why solvers answer `Unknown`: that `resourceLimitReached` is set exactly when the
  * resource limit (`--z3-rlimit`, `--cvc5-rlimit`) was exhausted, and `unrollBoundReached` exactly
  * when unrolling reached `--unroll-bound`.
  */
class ReasonsToUnknownSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses._

  // f(n) = if (n <= 0) 0 else f(n - 1)
  private val fID = FreshIdentifier("f")
  private val f = mkFunDef(fID)() { _ => (
    Seq("n" :: IntegerType()), IntegerType(), { case Seq(n) =>
      if_ (n <= E(BigInt(0))) { E(BigInt(0)) } else_ { FunctionInvocation(fID, Seq(), Seq(n - E(BigInt(1)))) }
    })
  }

  private val symbols = NoSymbols.withFunctions(Seq(f))
  private val program = InoxProgram(symbols)
  private given Symbols = symbols

  private val Seq(x, y, z) = Seq("x", "y", "z").map(Variable.fresh(_, IntegerType()))

  // Satisfiable only by a counterexample to Fermat's last theorem for n = 3: the solvers can't
  // decide it, so they run until they are stopped by their resource limit or a timeout.
  private val hard = andJoin(Seq(
    x > E(BigInt(0)), y > E(BigInt(0)), z > E(BigInt(0)),
    x * x * x + y * y * y === z * z * z
  ))

  // Holds by induction only, so unrolling never proves it: f(x) == 0 for every x
  private val needsInduction = Not(FunctionInvocation(fID, Seq(), Seq(x)) === E(BigInt(0)))

  private case class SmtSolver(name: String, available: () => Boolean, rlimit: IntOptionDef)

  private val smtSolvers = Seq(
    SmtSolver("smt-z3", () => SolverFactory.hasZ3, smtlib.optZ3Rlimit),
    SmtSolver("smt-cvc5", () => SolverFactory.hasCVC5, smtlib.optCVC5Rlimit)
  )

  /** Checks `expr` with a fresh solver and returns the response with the solver's flags
    * (resourceLimitReached, unrollBoundReached). The timeout keeps a failing test from hanging. */
  private def check(solver: String, options: Seq[OptionValue[?]], expr: Expr, timeout: Duration = 60.seconds)
    : (SolverResponse[program.Model, Set[Expr]], Boolean, Boolean) = {
    val ctx = TestContext(Options(optSelectedSolvers(Set(solver)) +: options))
    val factory = program.getSolver(ctx).withTimeout(timeout)
    val s = factory.getNewSolver()
    try {
      s.assertCnstr(expr)
      val res = s.check(Simple)
      (res, s.resourceLimitReached, s.unrollBoundReached)
    } finally factory.reclaim(s)
  }

  for (solver <- smtSolvers) {
    test(s"${solver.name}: exhausting the resource limit is reported") {
      assume(solver.available(), s"${solver.name} is not available")
      val (res, resourceOut, boundHit) = check(solver.name, Seq(solver.rlimit(1)), hard)
      assert(res == Unknown)
      assert(resourceOut)
      assert(!boundHit)
    }

    test(s"${solver.name}: answers within the resource limit aren't resource-outs") {
      assume(solver.available(), s"${solver.name} is not available")
      val (unsat, unsatOut, _) = check(solver.name, Seq(solver.rlimit(1)), x > E(BigInt(0)) && x < E(BigInt(0)))
      assert(unsat == Unsat)
      assert(!unsatOut)

      val (sat, satOut, _) = check(solver.name, Seq(solver.rlimit(1)), x > E(BigInt(0)))
      assert(sat == Sat)
      assert(!satOut)
    }

    test(s"${solver.name}: the reason describes the last check only") {
      assume(solver.available(), s"${solver.name} is not available")
      val ctx = TestContext(Options(Seq(optSelectedSolvers(Set(solver.name)), solver.rlimit(1))))
      val factory = program.getSolver(ctx).withTimeout(60.seconds)
      val s = factory.getNewSolver()
      try {
        s.push()
        s.assertCnstr(hard)
        assert(s.check(Simple) == Unknown)
        assert(s.resourceLimitReached)
        s.pop()

        s.assertCnstr(x > E(BigInt(0)))
        assert(s.check(Simple) == Sat)
        assert(!s.resourceLimitReached)
      } finally factory.reclaim(s)
    }

    test(s"${solver.name}: a timeout isn't a resource-out, even with a resource limit") {
      assume(solver.available(), s"${solver.name} is not available")
      // The limit is far beyond what the solver can spend within the timeout
      val (res, resourceOut, _) = check(solver.name, Seq(solver.rlimit(4000)), hard, timeout = 1.second)
      assert(res == Unknown)
      assert(!resourceOut)
    }

    test(s"${solver.name}: reaching the unroll bound is reported") {
      assume(solver.available(), s"${solver.name} is not available")
      val (res, resourceOut, boundHit) = check(solver.name, Seq(unrolling.optUnrollBound(2)), needsInduction)
      assert(res == Unknown)
      assert(boundHit)
      assert(!resourceOut)
    }
  }

  test("princess: reaching the unroll bound is reported") {
    val (res, resourceOut, boundHit) = check("princess", Seq(unrolling.optUnrollBound(2)), needsInduction)
    assert(res == Unknown)
    assert(boundHit)
    assert(!resourceOut)
  }

  test("no flag is set when the unroll bound isn't reached") {
    assume(SolverFactory.hasZ3, "smt-z3 is not available")
    // f(0) == 0 needs a single unfolding
    val (res, resourceOut, boundHit) =
      check("smt-z3", Seq(unrolling.optUnrollBound(2)), Not(FunctionInvocation(fID, Seq(), Seq(E(BigInt(0)))) === E(BigInt(0))))
    assert(res == Unsat)
    assert(!boundHit)
    assert(!resourceOut)
  }
}
