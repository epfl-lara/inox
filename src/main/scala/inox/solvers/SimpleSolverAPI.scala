/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

trait SimpleSolverAPI {
  protected val factory: SolverFactory

  import factory.program.trees._
  import SolverResponses._

  def solveVALID(expression: Expr): Option[Boolean] = {
    val s = factory.getNewSolver()
    import s._
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

  def solveSAT(expression: Expr): ResponseWithModel[Map[ValDef, Expr]] = {
    val s = factory.getNewSolver()
    import s._
    try {
      s.assertCnstr(expression)
      s.check(Model)
    } finally {
      factory.reclaim(s)
    }
  }

  def solveSATWithCores(expression: Expr, assumptions: Set[Expr]):
                        ResponseWithModelAndCores[Map[ValDef, Expr], Set[Expr]] = {
    val s = factory.getNewSolver()
    import s._
    try {
      s.assertCnstr(expression)
      s.checkAssumptions(All)(assumptions)
    } finally {
      factory.reclaim(s)
    }
  }
}

object SimpleSolverAPI {
  def apply(sf: SolverFactory) = new SimpleSolverAPI {
    val factory: sf.type = sf
  }
}
