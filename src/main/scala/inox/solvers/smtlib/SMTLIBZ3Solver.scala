/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

class SMTLIBZ3Solver(val program: Program, val options: SolverOptions)
  extends SMTLIBSolver
     with SMTLIBZ3Target
