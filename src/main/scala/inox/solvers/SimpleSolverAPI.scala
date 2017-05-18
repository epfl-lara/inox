/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

trait SimpleSolverAPI { self =>
  protected val program: Program
  type S <: Solver { val program: self.program.type }

  protected val factory: SolverFactory {
    val program: self.program.type
    type S = self.S
  }

  import program.trees._
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

  def solveSAT(expression: Expr): ResponseWithModel[Model { val program: self.program.type }] = {
    val s = factory.getNewSolver()
    try {
      s.assertCnstr(expression)
      s.check(Model)
    } finally {
      factory.reclaim(s)
    }
  }

  def solveSATWithUnsatAssumptions(expression: Expr, assumptions: Set[Expr]):
                                   ResponseWithModelAndAssumptions[Model { val program: self.program.type }, Set[Expr]] = {
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
  def apply(sf: SolverFactory): SimpleSolverAPI {
    val program: sf.program.type
    type S = sf.S
  } = new SimpleSolverAPI {
    val program: sf.program.type = sf.program
    type S = sf.S
    val factory = sf.asInstanceOf[SolverFactory { val program: sf.program.type; type S = sf.S }]
  }
}
