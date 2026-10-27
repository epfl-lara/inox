/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package tip

import solvers._

import scala.language.existentials

class TipTestSuite extends unrolling.UnrollingTestSuite with ResourceUtils {

  override protected def optionMatrix = unrolling.UnrollingTestSuite.combinations(
    Seq(optSilentErrors(false)),
    Seq(optCheckModels(true)),
    unrolling.UnrollingTestSuite.both(optAssumeChecked)
  )

  override protected def optionsString(options: Options): String = {
    "solver=" + options.findOptionOrDefault(optSelectedSolvers).head +
    (if (options.findOptionOrDefault(optAssumeChecked)) " assumechecked" else "")
  }

  // Benchmarks that the unrolling solver can't handle run on native Z3 instead
  private def onNativeZ3(ctx: Context): FilterStatus =
    WithContext(ctx.withOpts(optSelectedSolvers(Set("nativez3"))))

  // These compare functions, so they need function equality (see `optFunctionEquality`)
  private val comparingFunctions = Set(
    "Injective.scala-0.tip", "LambdaEquality2.scala-1.tip", "Streams.scala-0.tip", "inline-lambdas.scala-0.tip")

  private def withSemantics(ctx: Context, file: java.io.File): Context =
    if (comparingFunctions(file.getName)) {
      ctx.withOpts(unrolling.optFunctionEquality(unrolling.FunctionEquality.Intensional))
    } else {
      ctx
    }

  private def ignoreSAT(ctx: Context, file: java.io.File): FilterStatus = 
    ctx.options.findOptionOrDefault(optSelectedSolvers).headOption match {
      case Some(solver) => (solver, file.getName) match {
        // takes about 90s even on native Z3, so it only runs once
        case (_, "ForallAssoc.scala-0.tip") if ctx.options.findOptionOrDefault(optAssumeChecked) => Skip
        // Z3 and CVC4 binaries are exceedingly slow on these benchmarks
        case ("no-inc:smt-z3" | "smt-z3" | "smt-cvc4", "ForallAssoc.scala-0.tip") => onNativeZ3(ctx)
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
        case ("no-inc:smt-z3" | "smt-z3", "MergeSort2.scala-1.tip") => onNativeZ3(ctx)
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
        case ("smt-z3", "Soundness2.scala-0.tip") => onNativeZ3(ctx)
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
    test(s"SAT - ${file.getName}", ignoreSAT(_, file)) { ctx0 ?=>
      given inox.Context = withSemantics(ctx0, file)
      for ((program, expr) <- Parser(file).parseScript) {
        assert(SimpleSolverAPI(program.getSolver).solveSAT(expr).isSAT)
      }
    }
  }

  for (file <- resourceFiles("regression/tip/UNSAT", _.endsWith(".tip"))) {
    test(s"UNSAT - ${file.getName}", ignoreUNSAT(_, file)) { ctx0 ?=>
      given inox.Context = withSemantics(ctx0, file)
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

  for (dir <- Seq("SAT", "UNSAT"); file <- resourceFiles(s"regression/tip/$dir", name => comparingFunctions.exists(name.endsWith))) {
    test(s"REJECTED - ${file.getName}") {
      for ((program, expr) <- Parser(file).parseScript) {
        intercept[ast.TypeOps#TypeErrorException](SimpleSolverAPI(program.getSolver).solveSAT(expr))
      }
    }
  }
}
