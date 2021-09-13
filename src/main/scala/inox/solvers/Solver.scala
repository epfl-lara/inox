/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import utils._

object optCheckModels  extends FlagOptionDef("check-models", false)
object optSilentErrors extends FlagOptionDef("silent-errors", false)

case object DebugSectionSolver extends DebugSection("solver")

trait AbstractSolver extends Interruptible {
  def name: String
  val program: Program
  val context: Context

  import context._
  import program._
  import program.trees._

  type Trees
  type Model
  type Assumptions = Set[Trees]

  import SolverResponses._

  // This is ugly, but helpful for smtlib solvers
  def dbg(msg: => Any): Unit = {}

  object SolverUnsupportedError {
    def msg(t: Tree, reason: Option[String]) = {
      s"(of ${t.getClass}) is unsupported by solver $name" + reason.map(":\n  " + _ ).getOrElse("")
    }
  }

  case class SolverUnsupportedError(t: Tree, reason: Option[String] = None)
    extends UnsupportedTree(t, SolverUnsupportedError.msg(t,reason))

  protected def unsupported(t: Tree): Nothing = {
    throw SolverUnsupportedError(t, None)
  }

  protected def unsupported(t: Tree, str: String): Nothing = {
    throw SolverUnsupportedError(t, Some(str))
  }

  def assertCnstr(expression: Trees): Unit
  def check(config: CheckConfiguration): config.Response[Model, Assumptions]
  def checkAssumptions(config: Configuration)(assumptions: Set[Trees]): config.Response[Model, Assumptions]

  def free(): Unit

  def reset(): Unit

  def push(): Unit
  def pop(): Unit

  implicit val debugSection: DebugSection = DebugSectionSolver

  private[solvers] def debugS(msg: String) = {
    reporter.debug("["+name+"] "+msg)
  }

  override def toString: String = name
}

trait Solver extends AbstractSolver { self =>
  import program.trees._

  override type Trees = Expr
  override type Model = program.Model

  def declare(vd: ValDef): Unit

  def getResultSolver: Option[Solver] = Some(this)
}
