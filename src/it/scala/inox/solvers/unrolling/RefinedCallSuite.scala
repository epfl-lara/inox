/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class RefinedCallSuite extends ScriptTestSuite("refined-calls") {
  override protected def optionMatrix = Seq(Seq(optCheckModels(true)))
}
