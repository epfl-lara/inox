/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package tip

import solvers._

import scala.language.existentials

class TipTestSuite extends TestSuite with ResourceUtils {

  override def configurations = Seq(
    Seq(optSelectedSolvers(Set("nativez3")),      optSilentErrors(false), optCheckModels(true)),
    Seq(optSelectedSolvers(Set("smt-z3")),        optSilentErrors(false), optCheckModels(true)),
    Seq(optSelectedSolvers(Set("smt-cvc4")),      optSilentErrors(false), optCheckModels(true)),
    Seq(optSelectedSolvers(Set("smt-z3")),        optSilentErrors(false), optCheckModels(true), optAssumeChecked(true)),
    Seq(optSelectedSolvers(Set("no-inc:smt-z3")), optSilentErrors(false), optCheckModels(true))
  )

  override protected def optionsString(options: Options): String = {
    "solver=" + options.findOptionOrDefault(optSelectedSolvers).head +
    (if (options.findOptionOrDefault(optAssumeChecked)) " assumechecked" else "")
  }

  private def ignoreSAT(ctx: Context, file: java.io.File): FilterStatus = 
    ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
      case Some(solver) => (solver, file.getName) match {
        // Z3 and CVC4 binaries are exceedingly slow on these benchmarks
        case ("no-inc:smt-z3" | "smt-z3" | "smt-cvc4", "ForallAssoc.scala-0.tip") => Ignore
        // this test only holds when assumeChecked=false
        case (_, "LambdaEquality2.scala-1.tip") if ctx.options.findOptionOrDefault(optAssumeChecked) => Skip
        case _ => Test
      }

      case _ => Test
    }

  private def ignoreUNSAT(ctx: Context, file: java.io.File): FilterStatus = 
    ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
      case Some(solver) => (solver, file.getName) match {
        // Z3 binary will predictably segfault on certain permutations of this problem
        case ("no-inc:smt-z3" | "smt-z3", "MergeSort2.scala-1.tip") => Ignore
        // use non-linear operators that aren't supported in CVC4
        case ("smt-cvc4", "Instantiation.scala-0.tip") => Skip
        case ("smt-cvc4", "LetsInForall.tip") => Skip
        case ("smt-cvc4", "Weird.scala-0.tip") => Skip
        // this test only holds when assumeChecked=true
        case (_, "QuickSortFilter.scala-1.tip") if !ctx.options.findOptionOrDefault(optAssumeChecked) => Skip
        case _ => Test
      }
      case _ => Test
    }

  private def ignoreUNKNOWN(ctx: Context, file: java.io.File): FilterStatus = 
    ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
      case Some(solver) => (solver, file.getName) match {
        // non-linear operations are too slow on smt-z3
        case ("smt-z3", "Soundness2.scala-0.tip") => Ignore
        // use non-linear operators that aren't supported in CVC4
        case ("smt-cvc4", "Soundness.scala-0.tip") => Skip
        case ("smt-cvc4", "Soundness2.scala-0.tip") => Skip
        // Takes ~8 minutes to complete
        case ("no-inc:smt-z3", "Soundness3.scala-0.tip") => Skip
        case _ => Test
      }
      case _ => Test
    }

  for (file <- resourceFiles("regression/tip/SAT", _.endsWith(".tip"))) {
    test(s"SAT - ${file.getName}", ignoreSAT(_, file)) {
      for ((program, expr) <- Parser(file).parseScript) {
        assert(SimpleSolverAPI(program.getSolver).solveSAT(expr).isSAT)
      }
    }
  }

  for (file <- resourceFiles("regression/tip/UNSAT", _.endsWith(".tip"))) {
    test(s"UNSAT - ${file.getName}", ignoreUNSAT(_, file)) {
      for ((program, expr) <- Parser(file).parseScript) {
        assert(SimpleSolverAPI(program.getSolver).solveSAT(expr).isUNSAT)
      }
    }
  }

  for (file <- resourceFiles("regression/tip/UNKNOWN", _.endsWith(".tip"))) {
    test(s"UNKNOWN - ${file.getName}", ignoreUNKNOWN(_, file)) { ctx0 ?=>
      given ctx: inox.Context = ctx0.copy(options = ctx0.options + optCheckModels(false))
      for ((program, expr) <- Parser(file).parseScript) {
        val api = SimpleSolverAPI(program.getSolver)
        val res = api.solveSAT(expr)
        assert(!res.isSAT && !res.isUNSAT)
        assert(ctx.reporter.errorCount > 0)
      }
    }
  }
}
