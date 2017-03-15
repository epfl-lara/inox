/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

trait AbstractOptimizer extends AbstractSolver {
  def assertCnstr(expression: Trees, weight: Int): Unit
  def assertCnstr(expression: Trees, weight: Int, group: String): Unit
}

trait Optimizer extends AbstractOptimizer with Solver
