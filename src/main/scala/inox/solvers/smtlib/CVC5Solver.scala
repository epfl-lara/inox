/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers._

object optCVC5Options extends SetOptionDef[String] {
  val name = "solver:cvc5"
  val default = Set[String]()
  val elementParser = stringParser
  val usageRhs = "<cvc5-opt>"
}

trait CVC5Solver extends CVCSolver with CVC5Target {
  override def optCVCOptions: SetOptionDef[String] = optCVC5Options

  // Inox characters are UTF-16 code units, so restrict the string alphabet to the BMP
  // (by default, cvc5 uses all 0x30000 SMT-LIB characters).
  override protected def targetOpts: Seq[String] = Seq("--strings-alpha-card=65536")
}
