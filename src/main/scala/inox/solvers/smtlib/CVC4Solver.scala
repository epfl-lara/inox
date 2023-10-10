/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers._

object optCVC4Options extends SetOptionDef[String] {
  val name = "solver:cvc4"
  val default = Set[String]()
  val elementParser = stringParser
  val usageRhs = "<cvc4-opt>"
}

trait CVC4Solver extends CVCSolver with CVC4Target {
  override def optCVCOptions: SetOptionDef[String] = optCVC4Options
}
