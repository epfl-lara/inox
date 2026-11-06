/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers.z3

import z3.scala.{Z3Solver => ScalaZ3Solver, given, _}
import Z3Native._
import solvers._

import scala.language.implicitConversions

trait AbstractZ3Solver
  extends AbstractSolver
     with Z3Native {

  import program._
  import program.trees._
  import program.symbols.{given, _}

  import SolverResponses._

  val name = "z3"

  private val solver: ScalaZ3Solver = z3.mkSolver()

  // Z3 throws when it is interrupted during a push or pop. As for checks, the interrupted
  // query then ends as Unknown, so we record which pushes reached Z3 to pop only those.
  private var z3Scopes: List[Boolean] = Nil

  override def push(): Unit = {
    super.push()
    z3Scopes = tryZ3(solver.push()).isDefined :: z3Scopes
  }

  override def pop(): Unit = {
    super.pop()
    val pushed = z3Scopes.headOption.getOrElse(true)
    z3Scopes = z3Scopes.drop(1)
    if (pushed) tryZ3(solver.pop())
  }

  def assertCnstr(ast: Z3AST): Unit = tryZ3(solver.assertCnstr(ast))

  // NOTE @nv: this is very similar to code in NativeZ3Optimizer and UninterpretedZ3Solver but
  //           is difficult to merge due to small API differences between the native Z3
  //           solvers and optimizers.
  private def extractResult(config: Configuration)(res: => Option[Boolean]) =
    config.cast(tryZ3(res match {
      case Some(true) =>
        if (config.withModel) SatWithModel(solver.getModel())
        else Sat

      case Some(false) =>
        if (config.withUnsatAssumptions) UnsatWithAssumptions(solver.getUnsatCore().toSet.flatMap(extractNot))
        else Unsat

      case None => Unknown
    }).getOrElse(Unknown))

  def check(config: CheckConfiguration): config.Response[Z3Model, Set[Z3AST]] = extractResult(config)(solver.check())
  def checkAssumptions(config: Configuration)(assumptions: Set[Z3AST]) =
    extractResult(config)(solver.checkAssumptions(assumptions.toSeq*))
}