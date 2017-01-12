/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import solvers._

class TipTestSuite extends TestSuite with ResourceUtils {

  override def configurations = Seq(
    Seq(optSelectedSolvers(Set("nativez3")), optCheckModels(true)),
    Seq(optSelectedSolvers(Set("smt-z3")),   optCheckModels(true)),
    Seq(optSelectedSolvers(Set("smt-cvc4")), optCheckModels(true))
  )

  override protected def optionsString(options: Options): String = {
    "solver=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  for (file <- resourceFiles("regression/tip/SAT", _.endsWith(".tip"))) {
    test(s"SAT - ${file.getName}", ctx => if (
      // XXX: test containing list of booleans, so CVC4 will crash on this
      //      See http://church.cims.nyu.edu/bugzilla3/show_bug.cgi?id=500
      ctx.options.findOptionOrDefault(optSelectedSolvers) == Set("smt-cvc4") &&
      file.getName.endsWith("List-fold.tip")
    ) Ignore else Test) { ctx =>
      for ((syms, expr) <- new Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(expr).isSAT)
      }
    }
  }

  for (file <- resourceFiles("regression/tip/UNSAT", _.endsWith(".tip"))) {
    test(s"UNSAT - ${file.getName}") { ctx =>
      for ((syms, expr) <- new Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(expr).isUNSAT)
      }
    }
  }
}
