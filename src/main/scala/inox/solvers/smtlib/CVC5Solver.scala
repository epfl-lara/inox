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

object optCVC5Rlimit extends LongOptionDef("cvc5-rlimit", 0L, "<N>")

trait CVC5Solver extends CVCSolver with CVC5Target {
  import context.{given, _}

  override def optCVCOptions: SetOptionDef[String] = optCVC5Options

  override def interpreterOpts = {
    val rlimit = options.findOptionOrDefault(optCVC5Rlimit)
    super.interpreterOpts ++ (if (rlimit > 0) Seq(s"--rlimit=$rlimit") else Seq())
  }
}
