/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

class SMTLIBCVC4Solver(val program: Program, val options: SolverOptions)
  extends SMTLIBSolver
     with SMTLIBCVC4Target {

  def interpreterOps(ctx: InoxContext) = {
    Seq(
      "-q",
      "--produce-models",
      "--incremental",
      // "--dt-rewrite-error-sel", // Removing since it causes CVC4 to segfault on some inputs
      "--rewrite-divk",
      "--print-success",
      "--lang", "smt2.5"
    )
  }
}
