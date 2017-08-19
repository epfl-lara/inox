/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

trait SolvingTestSuite extends TestSuite {

  override def configurations = for {
    solverName        <- Seq("nativez3", "nativez3-opt", "unrollz3", "princess", "smt-z3", "smt-z3-opt", "smt-cvc4")
    checkModels       <- Seq(false, true)
    feelingLucky      <- Seq(false, true)
    unrollAssumptions <- Seq(false, true)
    assumeChecked     <- Seq(PurityOptions.Unchecked, PurityOptions.AssumeChecked)
    modelFinding      <- Seq(0, 1)
  } yield Seq(
    optSelectedSolvers(Set(solverName)),
    optCheckModels(checkModels),
    optAssumeChecked(assumeChecked),
    unrolling.optFeelingLucky(feelingLucky),
    unrolling.optUnrollAssumptions(unrollAssumptions),
    unrolling.optModelFinding(modelFinding),
    optTimeout(300),
    ast.optPrintUniqueIds(true)
  )

  override protected def optionsString(options: Options): String = {
    super.optionsString(options) +
    " assck=" + options.findOptionOrDefault(optAssumeChecked).assumeChecked +
    " model=" + options.findOptionOrDefault(unrolling.optModelFinding)
  }
}
