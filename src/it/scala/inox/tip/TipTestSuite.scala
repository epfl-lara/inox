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

  private def ignoreFile(solver: String, fileName: String): Boolean = {
    // test containing list of booleans, so CVC4 will crash on this
    // See http://church.cims.nyu.edu/bugzilla3/show_bug.cgi?id=500
    (solver == "smt-cvc4" && fileName.endsWith("List-fold.tip")) ||
    // Z3 binary will predictably segfault on certain permutations of this problem
    (solver == "smt-z3" && fileName.endsWith("MergeSort2.scala-1.tip"))
  }

  for (file <- resourceFiles("regression/tip/SAT", _.endsWith(".tip"))) {
    test(s"SAT - ${file.getName}", ctx =>
      ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
        case Some(solver) if ignoreFile(solver, file.getName) => Ignore
        case _ => Test
    }) { ctx =>
      for ((syms, expr) <- new Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(expr).isSAT)
      }
    }
  }

  for (file <- resourceFiles("regression/tip/UNSAT", _.endsWith(".tip"))) {
    test(s"UNSAT - ${file.getName}", ctx =>
      ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
        case Some(solver) if ignoreFile(solver, file.getName) => Ignore
        case _ => Test
    }) { ctx =>
      for ((syms, expr) <- new Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(expr).isUNSAT)
      }
    }
  }
}
