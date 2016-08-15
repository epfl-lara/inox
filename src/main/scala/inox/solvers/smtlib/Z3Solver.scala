/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.parser.Terms.{Identifier => _, _}
import _root_.smtlib.parser.CommandsResponses._

trait Z3Solver extends SMTLIBSolver with Z3Target {
  import program.trees._
  import SolverResponses._

  /** Z3 uses a non-standard syntax for check-sat-assuming, namely
    * {{{
    *   (check-sat a1 ... an)
    * }}}
    * so we have to use a [[_root_.smtlib.parser.Terms.SList]] to actually
    * send the command to the underlying smtlib solver.
    */
  override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]) = {
    val cmd = SList(SSymbol("check-sat") +: assumptions.toSeq.map(as => toSMT(as)(Map.empty)) : _*)
    val res = emit(cmd) match {
      case SSymbol("sat") => CheckSatStatus(SatStatus)
      case SSymbol("unsat") => CheckSatStatus(UnsatStatus)
      case res => res
    }
    extractResponse(config, res)
  }
}
