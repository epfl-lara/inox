/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers.*

object optBitwuzlaOptions extends SetOptionDef[String] {
  val name = "solver:bitwuzla"
  val default = Set[String]()
  val elementParser = stringParser
  val usageRhs = "<bitwuzla-opt>"
}

trait BitwuzlaSolver extends SMTLIBSolver with BitwuzlaTarget {

  import context.{given, _}
  import program.trees._
  import SolverResponses._


  def interpreterOpts = {
    Seq(
      "-v", "0", // quiet
      "--produce-models", // support the get-value and get-model commands
      "--lang", "smt2"
    ) ++ options.findOptionOrDefault(optBitwuzlaOptions)
  }

  override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[program.Model, Assumptions] = {
    push()
    for (cl <- assumptions) assertCnstr(cl)
    val res: SolverResponse[Model, Assumptions] = check(Model `min` config)
    pop()

    config.cast(res match {
      case Unsat if config.withUnsatAssumptions =>
        UnsatWithAssumptions(Set.empty)
      case _ => res
    })
  }
}
