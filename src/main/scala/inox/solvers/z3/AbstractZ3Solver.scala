/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers.z3

import z3.scala.{Z3Solver => ScalaZ3Solver, _}
import Z3Native._
import solvers._

trait AbstractZ3Solver
  extends AbstractSolver
     with Z3Native {

  import program._
  import program.trees._
  import program.symbols._

  import SolverResponses._

  val name = "z3"

  private[this] val solver: ScalaZ3Solver = z3.mkSolver()

  override def push(): Unit = {
    super.push()
    solver.push()
  }

  override def pop(): Unit = {
    super.pop()
    solver.pop()
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

  def check(config: CheckConfiguration) = extractResult(config)(solver.check())
  def checkAssumptions(config: Configuration)(assumptions: Set[Z3AST]) =
    extractResult(config)(solver.checkAssumptions(assumptions.toSeq : _*))
}
