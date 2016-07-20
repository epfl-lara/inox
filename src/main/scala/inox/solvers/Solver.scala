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

trait Solver extends Interruptible {
  def name: String
  val program: Program
  val options: SolverOptions

  import program._
  import program.trees._

  sealed trait SolverResponse
  case object Unknown extends SolverResponse

  sealed trait SolverUnsatResponse extends SolverResponse
  case object UnsatResponse extends SolverUnsatResponse
  case class UnsatResponseWithCores(cores: Set[Expr]) extends SolverUnsatResponse

  sealed trait SolverSatResponse extends SolverResponse
  case object SatResponse extends SolverSatResponse
  case class SatResponseWithModel(model: Map[ValDef, Expr]) extends SolverSatResponse

  object Check {
    def unapply(resp: SolverResponse): Option[Boolean] = resp match {
      case _: SolverUnsatResponse => Some(false)
      case _: SolverSatResponse   => Some(true)
      case Unknown => None
    }
  }

  object Sat {
    def unapply(resp: SolverSatResponse): Boolean = resp match {
      case SatResponse => true
      case SatResponseWithModel(_) => throw FatalError("Unexpected sat response with model")
      case _ => false
    }
  }

  object Model {
    def unapply(resp: SolverSatResponse): Option[Map[ValDef, Expr]] = resp match {
      case SatResponseWithModel(model) => Some(model)
      case SatResponse => throw FatalError("Unexpected sat response without model")
      case _ => None
    }
  }

  object Unsat {
    def unapply(resp: SolverUnsatResponse): Boolean = resp match {
      case UnsatResponse => true
      case UnsatResponseWithCores(_) => throw FatalError("Unexpected unsat response with cores")
      case _ => false
    }
  }

  object Core {
    def unapply(resp: SolverUnsatResponse): Option[Set[Expr]] = resp match {
      case UnsatResponseWithCores(cores) => Some(cores)
      case UnsatResponse => throw FatalError("Unexpected unsat response with cores")
      case _ => None
    }
  }

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

  def check(model: Boolean = false, cores: Boolean = false): SolverResponse
  def checkAssumptions(model: Boolean = false, cores: Boolean = false)(assumptions: Set[Expr]): SolverResponse
  
  def getResultSolver: Option[Solver] = Some(this)

  def free()

  def reset()

  def push(): Unit
  def pop(): Unit

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
