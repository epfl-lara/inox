/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package combinators

import scala.reflect.runtime.universe._

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

  override def reclaim(s: S) = sfs.zip(s.solvers).foreach { case (sf, s) =>
    sf.reclaim(s)
  }

  val name = sfs.map(_.name).mkString("Pfolio(", ",", ")")
}

