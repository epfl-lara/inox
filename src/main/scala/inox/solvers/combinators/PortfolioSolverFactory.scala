/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package combinators

trait PortfolioSolverFactory extends SolverFactory { self =>

  final type PT = program.type
  override type S = PortfolioSolver { val program: PT }
  final type SF = SolverFactory { val program: PT }

  val sfs: Seq[SF]

  def getNewSolver(): S = {
    new PortfolioSolver {
      val program: PT = self.program
      val solvers = sfs map (_.getNewSolver())
      val options: SolverOptions = solvers.head.options
    }
  }

  // Assumes s is a P/Solver with the correct subsolver types
  override def reclaim(s: S) = sfs.zip(s.solvers).foreach { case (sf, s) =>
    sf.reclaim(s.asInstanceOf[sf.S])
  }

  val name = sfs.map(_.name).mkString("Pfolio(", ",", ")")
}

