/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package combinators

object EncodingSolverFactory {
  def apply(p: Program)
           (enc: ast.ProgramEncoder { val sourceProgram: p.type })
           (sf: SolverFactory {
             val program: enc.targetProgram.type
             type S <: TimeoutSolver { val program: enc.targetProgram.type }
           }): SolverFactory {
             val program: p.type
             type S <: TimeoutSolver { val program: p.type }
           } = {

    SolverFactory.create(p)("E:" + sf.name, () => new {
      val program: p.type = p
    } with EncodingSolver with TimeoutSolver {
      val encoder: enc.type = enc
      val underlying = sf.getNewSolver()

      def interrupt() = underlying.interrupt()
      def recoverInterrupt() = underlying.recoverInterrupt()
    })
  }
}
