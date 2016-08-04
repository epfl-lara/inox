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

  import SolverResponses._

  sealed trait Configuration {
    type Response <: SolverResponse[Map[ValDef, Expr], Set[Expr]]

    def max(that: Configuration): Configuration = (this, that) match {
      case (All  , _    ) => All
      case (_    , All  ) => All
      case (Model, Cores) => All
      case (Cores, Model) => All
      case (Model, _    ) => Model
      case (_    , Model) => Model
      case (Cores, _    ) => Cores
      case (_    , Cores) => Cores
      case _              => Simple
    }

    def min(that: Configuration): Configuration = (this, that) match {
      case (o1, o2) if o1 == o2 => o1
      case (Simple, _) => Simple
      case (_, Simple) => Simple
      case (Model, Cores) => Simple
      case (Cores, Model) => Simple
      case (All, o) => o
      case (o, All) => o
    }

    def in(solver: Solver): solver.Configuration = this match {
      case Simple => solver.Simple
      case Model => solver.Model
      case Cores => solver.Cores
      case All => solver.All
    }

    def cast(resp: SolverResponse[Map[ValDef, Expr], Set[Expr]]): Response = ((this, resp) match {
      case (_             , Unknown)               => Unknown
      case (Simple | Cores, Sat)                   => Sat
      case (Model  | All  , s @ SatWithModel(_))   => s
      case (Simple | Model, Unsat)                 => Unsat
      case (Cores  | All  , u @ UnsatWithCores(_)) => u
      case _ => throw FatalError("Unexpected response " + resp + " for configuration " + this)
    }).asInstanceOf[Response]
  }

  object Configuration {
    def apply(model: Boolean = false, cores: Boolean = false): Configuration =
      if (model && cores) All
      else if (model) Model
      else if (cores) Cores
      else Simple
  }

  case object Simple extends Configuration { type Response = SimpleResponse }
  case object Model  extends Configuration { type Response = ResponseWithModel[Map[ValDef, Expr]] }
  case object Cores  extends Configuration { type Response = ResponseWithCores[Set[Expr]] }
  case object All    extends Configuration { type Response = ResponseWithModelAndCores[Map[ValDef, Expr], Set[Expr]] }

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

  def check[R](config: Configuration { type Response <: R }): R
  def checkAssumptions[R](config: Configuration { type Response <: R })(assumptions: Set[Expr]): R

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
