/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

trait AbstractOptimizer extends AbstractSolver {
  def assertCnstr(expression: Trees, weight: Int): Unit
  def assertCnstr(expression: Trees, weight: Int, group: String): Unit
  def minimize(expression: Trees): Unit
  def maximize(expression: Trees): Unit
}

trait Optimizer extends AbstractOptimizer with Solver
