/* Copyright 2009-2016 EPFL, Lausanne */

package inox

trait SolvingTestSuite extends InoxTestSuite {
  import solvers._

  override val configurations = for {
    solverName        <- Seq("nativez3", "unrollz3", "smt-z3", "smt-cvc4")
    checkModels       <- Seq(true, false)
    feelingLucky      <- Seq(true, false)
    unrollAssumptions <- Seq(true, false)
  } yield Seq(
    InoxOption(InoxOptions.optSelectedSolvers)(Set(solverName)),
    InoxOption(optCheckModels)(checkModels),
    InoxOption(unrolling.optFeelingLucky)(feelingLucky),
    InoxOption(unrolling.optUnrollAssumptions)(unrollAssumptions),
    InoxOption(InoxOptions.optTimeout)(300)
  )
}
