/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

class PortfolioSolverFactory private(override val program: Program, override val name: String)
                                    // Alias for `program`, as we cannot use `program` within `sfs`
                                    (val prog: program.type)
                                    (val sfs: Seq[SolverFactory { val program: prog.type }])
  extends SolverFactory { self =>

  def this(prog: Program, sfs: Seq[SolverFactory { val program: prog.type }]) =
    this(prog, sfs.map(_.name).mkString("Pfolio(", ",", ")"))(prog)(sfs)

  type S = PortfolioSolver with TimeoutSolver { val program: self.program.type }

  def getNewSolver(): S = {
    class Impl(override val program: self.program.type,
               override val context: inox.Context,
               override val solvers: Seq[Solver { val program: self.program.type }])
      extends PortfolioSolver with TimeoutSolver
    val solvers = sfs map (_.getNewSolver())
    new Impl(program, solvers.head.context, solvers)
  }

  // Assumes s is a P/Solver with the correct subsolver types
  override def reclaim(s: S) = s perform {
    sfs.zip(s.solvers).foreach { case (sf, s) =>
      sf.reclaim(s.asInstanceOf[sf.S])
    }
  }
}

object PortfolioSolverFactory {
  def apply(p: Program)
           (factories: Seq[SolverFactory { val program: p.type; type S <: TimeoutSolver }]):
            PortfolioSolverFactory { val program: p.type; type S <: TimeoutSolver } = {
    class Impl(override val program: p.type) extends PortfolioSolverFactory(program, factories)
    new Impl(p)
  }
}
