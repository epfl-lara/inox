/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers._

trait CVC4Solver extends SMTLIBSolver with CVC4Target {

  def interpreterOps(ctx: InoxContext) = {
    Seq(
      "-q",
      "--produce-models",
      "--incremental",
      // "--dt-rewrite-error-sel", // Removing since it causes CVC4 to segfault on some inputs
      "--rewrite-divk",
      "--print-success",
      "--lang", "smt2.5"
    ) ++ options.findOptionOrDefault(optCVC4Options)
  }
}

object optCVC4Options extends InoxOptionDef[Set[String]] {
  val name = "solver:cvc4"
  val description = "Pass extra arguments to CVC4"
  val default = Set[String]()
  val parser = setParser(stringParser)
  val usageRhs = "<cvc4-opt>"
}
