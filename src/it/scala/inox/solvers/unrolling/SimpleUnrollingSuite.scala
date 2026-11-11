/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class SimpleUnrollingSuite extends ScriptTestSuite("simple-unrolling") {
  import inox.trees._

  import SolverResponses._

  // Checks the configurations of the solver API, which scripts can't select
  test("simple configuration is sound with quantifiers") {
    val program = InoxProgram(NoSymbols)
    val factory = program.getSolver
    val c = Variable.fresh("c", IntegerType())
    val x = Variable.fresh("x", IntegerType())
    val expr = Forall(Seq(x.toVal), And(Equals(c, x), Equals(c, IntegerLiteral(42))))

    for (config <- Seq(Simple, Model)) {
      val solver = factory.getNewSolver()
      try {
        solver.assertCnstr(expr)
        val result = solver.check(config)
        assert(!result.isSAT && !result.isUNSAT, "Result should be unknown")
      } finally {
        factory.reclaim(solver)
      }
    }
  }
}
