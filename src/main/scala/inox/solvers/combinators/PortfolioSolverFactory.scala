/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

trait PortfolioSolverFactory extends SolverFactory { self =>

  type S = PortfolioSolver with TimeoutSolver { val program: self.program.type }
  type SF <: SolverFactory { val program: self.program.type }

  val sfs: Seq[SF]

  def getNewSolver(): S = {
    val newSolvers = sfs map (_.getNewSolver())

    class SolverBase(
      val program: self.program.type,
      val context: Context) extends PortfolioSolver with TimeoutSolver {

      val solvers = newSolvers.asInstanceOf[Seq[SubSolver]]
    }

    new SolverBase(self.program, newSolvers.head.context)
  }

  // Assumes s is a P/Solver with the correct subsolver types
  override def reclaim(s: S) = sfs.zip(s.solvers).foreach { case (sf, s) =>
    sf.reclaim(s.asInstanceOf[sf.S])
  }

  val name = sfs.map(_.name).mkString("Pfolio(", ",", ")")
}

object PortfolioSolverFactory {
  def apply(p: Program)
           (factories: Seq[SolverFactory { val program: p.type; type S <: TimeoutSolver }]):
            PortfolioSolverFactory { val program: p.type; type S <: TimeoutSolver } =
    new PortfolioSolverFactory {
      val program: p.type = p
      val sfs = factories

      type SF = SolverFactory { val program: p.type; type S <: TimeoutSolver }
    }
}
