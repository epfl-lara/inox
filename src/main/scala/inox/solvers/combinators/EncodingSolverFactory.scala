/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

object EncodingSolverFactory {
  def apply(p: Program)
           (enc: ast.ProgramTransformer { val sourceProgram: p.type })
           (sf: SolverFactory {
             val program: enc.targetProgram.type
             type S <: TimeoutSolver { val program: enc.targetProgram.type }
           }): SolverFactory {
             val program: p.type
             type S <: TimeoutSolver { val program: p.type }
           } = {

    class SolverBase(val program: p.type, val encoder: enc.type)
      extends EncodingSolver with TimeoutSolver {

      val underlying = sf.getNewSolver()
    }
    SolverFactory.create(p)("E:" + sf.name, () => new SolverBase(p, enc))
  }
}
