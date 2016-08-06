/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import scala.reflect.runtime.universe._

trait SolverFactory {
  val program: Program

  type S <: Solver { val program: SolverFactory.this.program.type }

  val name: String

  def getNewSolver(): S

  def shutdown(): Unit = {}

  def reclaim(s: S) {
    s.free()
  }
}

object SolverFactory {
  def create[S1 <: Solver : TypeTag](p: Program)(nme: String, builder: () => S1 { val program: p.type }):
           SolverFactory { val program: p.type; type S = S1 { val program: p.type } } = {
    new SolverFactory {
      val program: p.type = p
      type S = S1 { val program: p.type }

      val name = nme
      def getNewSolver() = builder()
    }
  }

  def apply(p: Program): SolverFactory { val program: p.type } = ???
}
