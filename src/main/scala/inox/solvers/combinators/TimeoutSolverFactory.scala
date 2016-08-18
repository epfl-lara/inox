/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package combinators

trait TimeoutSolverFactory extends SolverFactory {
  type S <: TimeoutSolver { val program: TimeoutSolverFactory.this.program.type }

  val factory: SolverFactory {
    val program: TimeoutSolverFactory.this.program.type
    type S = TimeoutSolverFactory.this.S
  }

  val to: Long

  override def getNewSolver() = factory.getNewSolver().setTimeout(to)

  override lazy val name = factory.name+" with t.o"

  override def reclaim(s: S) = factory.reclaim(s)

  override def shutdown() = factory.shutdown()
}

