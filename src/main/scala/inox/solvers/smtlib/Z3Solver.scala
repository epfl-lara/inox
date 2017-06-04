/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{Identifier => _, _}
import _root_.smtlib.trees.CommandsResponses._

trait Z3Solver extends SMTLIBSolver with Z3Target { self =>
  import program.trees._
  import SolverResponses._

  protected lazy val evaluator: evaluators.DeterministicEvaluator { val program: self.program.type } =
    semantics.getEvaluator(program.ctx.options + evaluators.optIgnoreContracts(true))

  // XXX @nv: Sometimes Z3 doesn't return fully evaluated models so we make sure to
  //          bring them into some normal form after extraction
  override protected def extractResponse(config: Configuration, res: SExpr) =
    config.cast(super.extractResponse(config, res) match {
      case SatWithModel(model) =>
        val evaluations = model.vars.map { case (k, v) => k -> evaluator.eval(v).result }
        SatWithModel(inox.Model(program)(evaluations.collect { case (k, Some(v)) => k -> v }, model.chooses))
      case resp => resp
    })

  /** Z3 uses a non-standard syntax for check-sat-assuming, namely
    * {{{
    *   (check-sat a1 ... an)
    * }}}
    * so we have to use a scala-smtlib `SList` to actually
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
