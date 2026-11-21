/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import inox.OptionParsers.*

object cvcSimplesModelOpt extends FlagOptionDef(name = "cvc-simple-models", default = false)

trait CVCSolver extends SMTLIBSolver with CVCTarget {
  import context.{given, _}
  import program.trees._
  import SolverResponses._

  def optCVCOptions: SetOptionDef[String]

  /** Solver-specific options, which can be overridden by the user-provided ones. */
  protected def targetOpts: Seq[String] = Seq.empty

  def interpreterOpts = {
    Seq(
      "-q", // quiet
      "--produce-models", // support the get-value and get-model commands
      "--incremental",
      "--print-success",
      "--lang", "smt2.6"
    ) ++ (if options.findOptionOrDefault(cvcSimplesModelOpt) then Seq("--model-cores", "simple") else Seq())
      ++ targetOpts
      ++ options.findOptionOrDefault(optCVCOptions)
  }

  /** The proof that the session has no model, after an unsat check (while its assumptions are
    * still asserted), or why there is none: a check with proofs answers unsat with it. */
  protected def proof(): Either[String, certificates.Proof] = Left("the solver does not produce proofs")

  override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[program.Model, Assumptions] = {
    push()
    for (cl <- assumptions) assertCnstr(cl)
    val res: SolverResponse[Model, Assumptions] = check(Model `min` config) match {
      case Unsat if config.withProof => UnsatWithProof(proof())
      case res => res
    }
    pop()

    config.cast(res match {
      case Unsat if config.withUnsatAssumptions =>
        UnsatWithAssumptions(Set.empty)
      case _ => res
    })
  }
}

