/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import utils._

object optCheckModels  extends FlagOptionDef("checkmodels", false)
object optSilentErrors extends FlagOptionDef("silenterrors", false)

case object DebugSectionSolver extends DebugSection("solver")

trait AbstractSolver extends Interruptible {
  def name: String
  val program: Program
  val options: Options

  import program._
  import program.trees._

  type Trees
  type Model
  type Assumptions = Set[Trees]

  import SolverResponses._

  lazy val reporter = program.ctx.reporter

  // This is ugly, but helpful for smtlib solvers
  def dbg(msg: => Any) {}

  object SolverUnsupportedError {
    def msg(t: Tree, reason: Option[String]) = {
      s"(of ${t.getClass}) is unsupported by solver $name" + reason.map(":\n  " + _ ).getOrElse("")
    }
  }

  case class SolverUnsupportedError(t: Tree, reason: Option[String] = None)
    extends Unsupported(t, SolverUnsupportedError.msg(t,reason))

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

  def assertCnstr(expression: Trees): Unit

  def check(config: CheckConfiguration): config.Response[Model, Assumptions]
  def checkAssumptions(config: Configuration)(assumptions: Set[Trees]): config.Response[Model, Assumptions]

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
  import program.trees._

  type Trees = Expr
  type Model = Map[ValDef, Expr]

  def getResultSolver: Option[Solver] = Some(this)
}
