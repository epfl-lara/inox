/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class ChooseSuite extends ScriptTestSuite("choose") {
  override protected def optionMatrix = Seq(Seq(optCheckModels(true)))
}
