/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import scala.reflect.runtime.universe._

abstract class SolverFactory[+S <: Solver] {
  def getNewSolver(): S

  def shutdown(): Unit = {}

  def reclaim(s: Solver) {
    s.free()
  }

  val name: String
}

object SolverFactory {
  def apply[S <: Solver : TypeTag](nme: String, builder: () => S): SolverFactory[S] = {
    new SolverFactory[S] {
      val name = nme
      def getNewSolver() = builder()
    }
  }
}
