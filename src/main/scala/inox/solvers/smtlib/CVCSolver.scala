/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers.*

trait CVCSolver extends SMTLIBSolver with CVCTarget {
  import context.{given, _}
  import program.trees._
  import SolverResponses._

  def optCVCOptions: SetOptionDef[String]

  def interpreterOpts = {
    Seq(
      "-q", // quiet
      "--produce-models", // support the get-value and get-model commands
      "--incremental",
      "--print-success",
      "--lang", "smt2.6"
    ) ++ options.findOptionOrDefault(optCVCOptions)
  }

  override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[program.Model, Assumptions] = {
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

