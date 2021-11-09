/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

object EncodingSolverFactory {
  def apply(p: Program)
           (enc: transformers.ProgramTransformer { val sourceProgram: p.type })
           (sf: SolverFactory {
             val program: enc.targetProgram.type
             type S <: TimeoutSolver { val program: enc.targetProgram.type }
           }): SolverFactory {
             val program: p.type
             type S <: TimeoutSolver { val program: p.type }
           } = {
    class Impl(override val program: p.type)
      extends EncodingSolver(p, enc, sf.getNewSolver()) with TimeoutSolver

    SolverFactory.create(p)("E:" + sf.name, () => new Impl(p))
  }
}
