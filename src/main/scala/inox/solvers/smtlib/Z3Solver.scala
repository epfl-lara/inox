/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{Identifier => _, _}
import _root_.smtlib.trees.CommandsResponses._

trait Z3Solver extends SMTLIBSolver with Z3Target { self =>
  import program.trees._
  import SolverResponses._

  // Completes the solver's models, in which function values are compared as such. The evaluation
  // of a huge model stops when the solver is interrupted (see `RecursiveEvaluator.e`).
  protected lazy val evalContext: inox.Context =
    context.copy(interruptManager = new inox.utils.InterruptManager(context.reporter)).withOpts(
      evaluators.optIgnoreContracts(true),
      evaluators.optSolveUninterpretedCalls(false),
      unrolling.optFunctionEquality(unrolling.FunctionEquality.Intensional))

  override def interrupt(): Unit = {
    super.interrupt()
    if (!evalContext.interruptManager.isInterrupted) evalContext.interruptManager.interrupt()
  }

  override def reset(): Unit = {
    super.reset()
    if (evalContext.interruptManager.isInterrupted) evalContext.interruptManager.reset()
  }

  // XXX @nv: Sometimes Z3 doesn't return fully evaluated models so we make sure to
  //          bring them into some normal form after extraction
  override protected def extractResponse(
    config: Configuration,
    res: SExpr,
    assumptions: Set[Expr]
  ): config.Response[Model, Assumptions] = config.cast(super.extractResponse(config, res, assumptions) match {
    case SatWithModel(model) =>
      val evaluator = semantics.getEvaluator(using evalContext)
      // An interrupted solver gives up on its model, whose answer is discarded anyway
      val evaluations = model.vars.iterator.takeWhile(_ => !aborted).map { case (k, v) => k -> evaluator.eval(v).result }.toMap
      if (aborted) Unknown
      else SatWithModel(inox.Model(program)(
        evaluations.collect { case (k, Some(v)) => k -> v },
        model.chooses
      ))
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
    // make sure assumptions are well-formed and contain only declared variables
    assumptions.foreach {
      case Not(v: Variable) => declareVariable(v)
      case v: Variable => declareVariable(v)
      case t => unsupported(t, "Assumptions must be either variables or their negation")
    }

    val cmd = SList(SSymbol("check-sat") +: assumptions.toSeq.map(as => toSMT(as)(using Map.empty))*)
    val res = emit(cmd) match {
      case SSymbol("sat") => CheckSatStatus(SatStatus)
      case SSymbol("unsat") => CheckSatStatus(UnsatStatus)
      case res => res
    }
    extractResponse(config, res, assumptions)
  }
}
