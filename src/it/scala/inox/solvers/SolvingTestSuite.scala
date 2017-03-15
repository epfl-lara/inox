/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

trait SolvingTestSuite extends TestSuite {

  override def configurations = for {
    solverName        <- Seq("nativez3", "nativez3-opt", "unrollz3", "princess", "smt-z3", "smt-z3-opt", "smt-cvc4")
    checkModels       <- Seq(false, true)
    feelingLucky      <- Seq(false, true)
    unrollAssumptions <- Seq(false, true)
  } yield Seq(
    optSelectedSolvers(Set(solverName)),
    optCheckModels(checkModels),
    unrolling.optFeelingLucky(feelingLucky),
    unrolling.optUnrollAssumptions(unrollAssumptions),
    optTimeout(300),
    ast.optPrintUniqueIds(true)
  )
}
