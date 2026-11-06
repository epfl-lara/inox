/* Copyright 2009-2020 EPFL, Lausanne */

package inox
package solvers
package unrolling

class MapMergeSuite extends ScriptTestSuite("map-merge") {
  override protected def optionMatrix = UnrollingTestSuite.combinations(
    Seq(optCheckModels(true)),
    UnrollingTestSuite.both(optFeelingLucky)
  )

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(optFeelingLucky)
  }
}
