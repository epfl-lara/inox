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
    InoxOptions.optSelectedSolvers(Set(solverName)),
    optCheckModels(checkModels),
    unrolling.optFeelingLucky(feelingLucky),
    unrolling.optUnrollAssumptions(unrollAssumptions),
    InoxOptions.optTimeout(300),
    ast.optPrintUniqueIds(true)
  )
}
