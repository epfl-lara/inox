/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import solvers._

import scala.language.existentials

class TipTestSuite extends TestSuite with ResourceUtils {

  override def configurations = Seq(
    Seq(optSelectedSolvers(Set("nativez3")), optCheckModels(true)),
    Seq(optSelectedSolvers(Set("smt-z3")),   optCheckModels(true)),
    Seq(optSelectedSolvers(Set("smt-cvc4")), optCheckModels(true)),
    Seq(optSelectedSolvers(Set("smt-z3")),   optCheckModels(true), optAssumeChecked(PurityOptions.AssumeChecked))
  )

  override protected def optionsString(options: Options): String = {
    "solver=" + options.findOptionOrDefault(optSelectedSolvers).head +
    (if (options.findOptionOrDefault(optAssumeChecked).assumeChecked) " assumechecked" else "")
  }

  private def ignoreSAT(ctx: Context, file: java.io.File): FilterStatus = 
    ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
      case Some(solver) => (solver, file.getName) match {
        // test containing list of booleans, so CVC4 will crash on this
        // See http://church.cims.nyu.edu/bugzilla3/show_bug.cgi?id=500
        case ("smt-cvc4", "List-fold.tip") => Skip
        // Z3 and CVC4 binaries are exceedingly slow on this benchmark
        case ("smt-z3", "BinarySearchTreeQuant.scala-2.tip") => Ignore
        case ("smt-cvc4", "BinarySearchTreeQuant.scala-2.tip") => Ignore
        // this test only holds when assumeChecked=false
        case (_, "LambdaEquality2.scala-1.tip")
        if ctx.options.findOptionOrDefault(optAssumeChecked).assumeChecked => Skip
        case _ => Test
      }

      case _ => Test
    }

  private def ignoreUNSAT(ctx: Context, file: java.io.File): FilterStatus = 
    ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
      case Some(solver) => (solver, file.getName) match {
        // Z3 binary will predictably segfault on certain permutations of this problem
        case ("smt-z3", "MergeSort2.scala-1.tip") => Ignore
        // use non-linear operators that aren't supported in CVC4
        case ("smt-cvc4", "Instantiation.scala-0.tip") => Skip
        case ("smt-cvc4", "LetsInForall.tip") => Skip
        case ("smt-cvc4", "Weird.scala-0.tip") => Skip
        case _ => Test
      }
      case _ => Test
    }

  private def ignoreUNKNOWN(ctx: Context, file: java.io.File): FilterStatus = 
    ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
      case Some(solver) => (solver, file.getName) match {
        // use non-linear operators that aren't supported in CVC4
        case ("smt-cvc4", "Soundness.scala-0.tip") => Skip
        case ("smt-cvc4", "Soundness2.scala-0.tip") => Skip
        case _ => Test
      }
      case _ => Test
    }

  for (file <- resourceFiles("regression/tip/SAT", _.endsWith(".tip"))) {
    test(s"SAT - ${file.getName}", ignoreSAT(_, file)) { ctx =>
      for ((syms, expr) <- new Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        assert(SimpleSolverAPI(program.getSolver).solveSAT(expr).isSAT)
      }
    }
  }

  for (file <- resourceFiles("regression/tip/UNSAT", _.endsWith(".tip"))) {
    test(s"UNSAT - ${file.getName}", ignoreUNSAT(_, file)) { ctx =>
      for ((syms, expr) <- new Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        assert(SimpleSolverAPI(program.getSolver).solveSAT(expr).isUNSAT)
      }
    }
  }

  for (file <- resourceFiles("regression/tip/UNKNOWN", _.endsWith(".tip"))) {
    test(s"UNKNOWN - ${file.getName}", ignoreUNKNOWN(_, file)) { ctx0 =>
      val ctx = ctx0.copy(options = ctx0.options + optCheckModels(false))
      for ((syms, expr) <- new Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        val api = SimpleSolverAPI(program.getSolver)
        val res = api.solveSAT(expr)
        assert(!res.isSAT && !res.isUNSAT)
        assert(ctx.reporter.errorCount > 0)
      }
    }
  }
}
