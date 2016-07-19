/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import utils._
import evaluators._

case class SolverOptions(options: Seq[InoxOption[Any]]) {
  def set(opts: Seq[LeonOption[Any]]): SolverOptions = {
    val changed = opts.map(_.optionDef).toSet
    val remainingOpts = options.filter { case InoxOption(optDef, _) => !changed(optDef) }
    copy(options = remainingOpts ++ opts)
  }
}

case object DebugSectionSolver extends DebugSection("solver")

trait Solver extends Interruptible {
  def name: String
  val program: Program
  val options: SolverOptions

  import program._
  import program.trees._

  sealed trait SolverResponse
  sealed trait SolverCheckResponse extends SolverResponse
  sealed trait SolverModelResponse extends SolverResponse

  case object Unknown extends SolverCheckResponse with SolverModelResponse
  case object UNSAT extends SolverCheckResponse with SolverModelResponse
  case object SAT extends SolverCheckResponse
  case class Model(model: Map[ValDef, Expr]) extends SolverModelResponse

  object SolverUnsupportedError {
    def msg(t: Tree, reason: Option[String]) = {
      s"(of ${t.getClass}) is unsupported by solver ${name}" + reason.map(":\n  " + _ ).getOrElse("")
    }
  }

  case class SolverUnsupportedError(t: Tree, reason: Option[String] = None)
    extends Unsupported(t, SolverUnsupportedError.msg(t,reason))

  lazy val reporter = program.ctx.reporter

  // This is ugly, but helpful for smtlib solvers
  def dbg(msg: => Any) {}

  def assertCnstr(expression: Expr): Unit

  /** Returns Some(true) if it found a satisfying model, Some(false) if no model exists, and None otherwise */
  def check: Option[Boolean]
  /** Returns the model if it exists */
  def getModel: Model
  def getResultSolver: Option[Solver] = Some(this)

  def free()

  def reset()

  def push(): Unit
  def pop(): Unit

  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean]
  def getUnsatCore: Set[Expr]

  protected def unsupported(t: Tree): Nothing = {
    val err = SolverUnsupportedError(t, None)
    reporter.warning(err.getMessage)
    throw err
  }

  protected def unsupported(t: Tree, str: String): Nothing = {
    val err = SolverUnsupportedError(t, Some(str))
    reporter.warning(err.getMessage)
    throw err
  }

  implicit val debugSection = DebugSectionSolver

  private[solvers] def debugS(msg: String) = {
    reporter.debug("["+name+"] "+msg)
  }
}
