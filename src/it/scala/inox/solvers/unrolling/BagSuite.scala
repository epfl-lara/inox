/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class BagSuite extends ScriptTestSuite("bags") {
  override protected def optionMatrix = UnrollingTestSuite.combinations(
    Seq(optCheckModels(true)),
    UnrollingTestSuite.both(optFeelingLucky)
  )

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(optFeelingLucky)
  }

  override protected def filter(ctx: Context, file: java.io.File): FilterStatus = {
    val solvers = ctx.options.findOptionOrDefault(optSelectedSolvers)
    // @nv: this test is unstable due to bugs in z3, so it runs on cvc5 instead
    if (file.getName == "split2-doesnt-preserve-content.smt3" && (solvers == Set("unrollz3") || solvers == Set("smt-z3")))
      WithContext(ctx.withOpts(optSelectedSolvers(Set("smt-cvc5"))))
    else Test
  }
}
