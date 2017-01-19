/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

trait SimpleSolverAPI {
  protected val factory: SolverFactory

  import factory.program.trees._
  import SolverResponses._

  def solveVALID(expression: Expr): Option[Boolean] = {
    val s = factory.getNewSolver()
    try {
      s.assertCnstr(Not(expression))
      s.check(Simple) match {
        case Check(r) => Some(!r)
        case _ => None
      }
    } finally {
      factory.reclaim(s)
    }
  }

  def solveSAT(expression: Expr): ResponseWithModel[Model { val program: factory.program.type }] = {
    val s = factory.getNewSolver()
    try {
      s.assertCnstr(expression)
      s.check(Model)
    } finally {
      factory.reclaim(s)
    }
  }

  def solveSATWithUnsatAssumptions(expression: Expr, assumptions: Set[Expr]):
                                   ResponseWithModelAndAssumptions[Model { val program: factory.program.type }, Set[Expr]] = {
    val s = factory.getNewSolver()
    try {
      s.assertCnstr(expression)
      s.checkAssumptions(All)(assumptions)
    } finally {
      factory.reclaim(s)
    }
  }
}

object SimpleSolverAPI {
  def apply(sf: SolverFactory): SimpleSolverAPI { val factory: sf.type } = new SimpleSolverAPI {
    val factory: sf.type = sf
  }
}
