/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import utils._
import evaluators._

case class SolverOptions(options: Seq[InoxOption[Any]]) extends InoxOptions {
  def set(opts: Seq[InoxOption[Any]]): SolverOptions = {
    val changed = opts.map(_.optionDef).toSet
    val remainingOpts = options.filter { case InoxOption(optDef, _) => !changed(optDef) }
    copy(options = remainingOpts ++ opts)
  }

  def set(opt: InoxOption[Any], opts: InoxOption[Any]*): SolverOptions = set(opt +: opts)
}

case object DebugSectionSolver extends DebugSection("solver")

object optCheckModels  extends InoxFlagOptionDef("checkmodels",  "Double-check counter-examples with evaluator", false)
object optSilentErrors extends InoxFlagOptionDef("silenterrors", "Fail silently into UNKNOWN when encountering an error", false)

trait AbstractSolver extends Interruptible {
  def name: String
  val program: Program
  val options: SolverOptions

  type Trees
  type Model
  type Cores

  import SolverResponses._

  lazy val reporter = program.ctx.reporter

  // This is ugly, but helpful for smtlib solvers
  def dbg(msg: => Any) {}

  def assertCnstr(expression: Trees): Unit

  def check(config: Configuration): config.Response[Model, Cores]
  def checkAssumptions(config: Configuration)(assumptions: Set[Trees]): config.Response[Model, Cores]

  def free(): Unit

  def reset(): Unit

  def push(): Unit
  def pop(): Unit

  implicit val debugSection = DebugSectionSolver

  private[solvers] def debugS(msg: String) = {
    reporter.debug("["+name+"] "+msg)
  }
}

trait Solver extends AbstractSolver {
  import program._
  import program.trees._

  type Trees = Expr
  type Model = Map[ValDef, Expr]
  type Cores = Set[Expr]

  object SolverUnsupportedError {
    def msg(t: Tree, reason: Option[String]) = {
      s"(of ${t.getClass}) is unsupported by solver ${name}" + reason.map(":\n  " + _ ).getOrElse("")
    }
  }

  case class SolverUnsupportedError(t: Tree, reason: Option[String] = None)
    extends Unsupported(t, SolverUnsupportedError.msg(t,reason))

  def getResultSolver: Option[Solver] = Some(this)

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
}
