/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.z3

import com.microsoft.z3.Z3Exception

import utils._

import z3.scala.{Z3Solver => ScalaZ3Solver, _}
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

  def assertCnstr(ast: Z3AST): Unit = solver.assertCnstr(ast)

  private def extractResult(config: Configuration)(res: => Option[Boolean]) = config.cast(try {
    res match {
      case Some(true) =>
        if (config.withModel) SatWithModel(solver.getModel)
        else Sat

      case Some(false) =>
        if (config.withUnsatAssumptions) UnsatWithAssumptions(solver.getUnsatCore.toSet.flatMap(extractNot))
        else Unsat

      case None => Unknown
    }
  } catch {
    // @nv: Z3 sometimes throws an exceptiopn when check is called after Z3 has been canceled
    case e: Z3Exception if e.getMessage == "canceled" => Unknown
  })

  def check(config: CheckConfiguration) = extractResult(config)(solver.check)
  def checkAssumptions(config: Configuration)(assumptions: Set[Z3AST]) =
    extractResult(config)(solver.checkAssumptions(assumptions.toSeq : _*))
}
