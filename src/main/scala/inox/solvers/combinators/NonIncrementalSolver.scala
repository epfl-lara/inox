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

  // Used to report SMT Lib files <-> VCs correspondence
  override def getSmtLibFileId: Option[Int] = currentSolver match
    case Some(solver) => solver.getSmtLibFileId
    case None => None

  val assertions: IncrementalSeq[Trees] = new IncrementalSeq[Trees]

  var currentSolver: Option[AbstractSolver] = None

  def assertCnstr(expression: Trees): Unit = assertions += expression
  def reset(): Unit = assertions.clear()
  def free(): Unit = for (solver <- currentSolver) solver.free()

  var interrupted = false

  def interrupt(): Unit = {
    val optSolver = synchronized {
      interrupted = true
      currentSolver
    }
    for (solver <- optSolver) solver.interrupt()
  }

  override def check(config: CheckConfiguration): config.Response[Model, Assumptions] = {
    assert(currentSolver.isEmpty,
      "`currentSolver` should be empty when invoking `check` in NonIncrementalSolver")
    val newSolver = underlying()
    try {
      val runCheck = synchronized {
        currentSolver = Some(newSolver)
        !interrupted
      }
      if (runCheck) {
        for (expression <- assertions)
          newSolver.assertCnstr(expression)
        val res = newSolver.check(config)
        currentSolver = None
        res
      } else {
        currentSolver = None
        config.cast(SolverResponses.Unknown)
      }
    } finally {
      newSolver.free()
    }
  }

  override def checkAssumptions(config: Configuration)
                               (assumptions: Set[Trees]): config.Response[Model, Assumptions] = {
    assert(currentSolver.isEmpty,
      "`currentSolver` should be empty when invoking `checkAssumptions` in NonIncrementalSolver")
    val newSolver = underlying()
    try {
      val runCheck = synchronized {
        currentSolver = Some(newSolver)
        !interrupted
      }
      if (runCheck) {
        for (expression <- assertions)
          newSolver.assertCnstr(expression)
        // we assert the assumptions to address: https://github.com/Z3Prover/z3/issues/5257
        for (assumption <- assumptions)
          newSolver.assertCnstr(assumption)
        val res = newSolver.checkAssumptions(config)(Set())
        currentSolver = None
        res
      } else {
        currentSolver = None
        config.cast(SolverResponses.Unknown)
      }
    } finally {
      newSolver.free()
    }
  }

  def push(): Unit = assertions.push()
  def pop(): Unit = assertions.pop()
}
