/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

class TimeoutSolverFactory private
  (override val program: Program, override val name: String, val to: Long)
  // Alias for `program`, as we cannot use `program` within `typeTagS` and `factory`
  (val prog: program.type)
  (val typeTagS: { type S <: TimeoutSolver { val program: prog.type } })
  (val factory: SolverFactory {
    val program: prog.type
    type S = typeTagS.S
  })
  extends SolverFactory {

  type S = typeTagS.S

  def this(prog: Program, to: Long,
           typeTagS: { type S <: TimeoutSolver { val program: prog.type } },
           factory: SolverFactory {
             val program: prog.type
             type S = typeTagS.S
           }) =
    this(prog, factory.name + " with t.o", to)(prog)(typeTagS)(factory)

  override def getNewSolver() = factory.getNewSolver().setTimeout(to)

  override def reclaim(s: S) = factory.reclaim(s)

  override def shutdown() = factory.shutdown()
}

