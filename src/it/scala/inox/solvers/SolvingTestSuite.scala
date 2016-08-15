/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

trait SolvingTestSuite extends InoxTestSuite {

  override val configurations = for {
    solverName        <- Seq("nativez3", "unrollz3", "smt-z3", "smt-cvc4")
    checkModels       <- Seq(false, true)
    feelingLucky      <- Seq(false, true)
    unrollAssumptions <- Seq(false, true)
  } yield Seq(
    InoxOption(InoxOptions.optSelectedSolvers)(Set(solverName)),
    InoxOption(optCheckModels)(checkModels),
    InoxOption(unrolling.optFeelingLucky)(feelingLucky),
    InoxOption(unrolling.optUnrollAssumptions)(unrollAssumptions),
    InoxOption(InoxOptions.optTimeout)(300),
    InoxOption(ast.optPrintUniqueIds)(true)
  )
}
