/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

import utils._
import scala.concurrent.duration._
import scala.collection.mutable.ArrayBuffer

trait NonIncrementalSolver extends AbstractSolver { self =>
  import program.trees._
  import SolverResponses._

  protected def underlying(): AbstractSolver {
    val program: self.program.type
    type Trees = self.Trees
    type Model = self.Model
  }

  val assertions: IncrementalSet[Trees] = new IncrementalSet[Trees]

  val allSolvers: ArrayBuffer[AbstractSolver] = ArrayBuffer()

  def assertCnstr(expression: Trees): Unit = assertions += expression
  def reset(): Unit = assertions.clear()
  def free(): Unit = for (solver <- allSolvers) solver.free()
  def interrupt(): Unit = for (solver <- allSolvers) solver.interrupt()

  override def check(config: CheckConfiguration): config.Response[Model, Assumptions] = {
    val newSolver = underlying()
    allSolvers.append(newSolver)
    for (expression <- assertions)
      newSolver.assertCnstr(expression)
    newSolver.check(config)
  }

  override def checkAssumptions(config: Configuration)
                               (assumptions: Set[Trees]): config.Response[Model, Assumptions] = {
    val newSolver = underlying()
    allSolvers.append(newSolver)
    for (expression <- assertions)
      newSolver.assertCnstr(expression)
    newSolver.checkAssumptions(config)(assumptions)
  }

  def push(): Unit = assertions.push()
  def pop(): Unit = assertions.pop()
}
