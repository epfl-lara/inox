/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers._

object optCVC4Options extends OptionDef[Set[String]] {
  val name = "solver:cvc4"
  val default = Set[String]()
  val parser = setParser(stringParser)
  val usageRhs = "<cvc4-opt>"
}

trait CVC4Solver extends SMTLIBSolver with CVC4Target {
  import program.trees._
  import SolverResponses._

  def interpreterOpts = {
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

  override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]) = {
    push()
    for (cl <- assumptions) assertCnstr(cl)
    val res: SolverResponse[Model, Assumptions] = check(Model min config)
    pop()

    config.cast(res match {
      case Unsat if config.withUnsatAssumptions =>
        UnsatWithAssumptions(Set.empty)
      case _ => res
    })
  }
}

