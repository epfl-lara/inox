/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.z3

import z3.scala._

import solvers._
import utils.IncrementalSet

/** This is a rather direct mapping to Z3, where all functions are left uninterpreted.
 *  It reports the results as follows (based on the negation of the formula):
 *    - if Z3 reports UNSAT, it reports VALID
 *    - if Z3 reports SAT and the formula contained no function invocation, it returns INVALID with the counter-example/model
 *    - otherwise it returns UNKNOWN
 *  Results should come back very quickly.
 */
trait UninterpretedZ3Solver
  extends Solver { self =>

  import program._
  import program.trees._
  import program.symbols._

  import SolverResponses._

  protected implicit val semantics: program.Semantics

  val name = "z3-u"
  val description = "Uninterpreted Z3 Solver"

  private object underlying extends {
    val program: self.program.type = self.program
    val options = self.options
  } with AbstractZ3Solver {
    val semantics = self.semantics
  }

  private val freeVars = new IncrementalSet[Variable]

  def push(): Unit = {
    underlying.push()
    freeVars.push()
  }

  def pop(): Unit = {
    underlying.pop()
    freeVars.pop()
  }

  def reset(): Unit = {
    underlying.reset()
    freeVars.reset()
  }

  def free(): Unit = underlying.free()

  def interrupt(): Unit = underlying.interrupt()

  def assertCnstr(expression: Expr) {
    freeVars ++= exprOps.variablesOf(expression)
    underlying.assertCnstr(underlying.toZ3Formula(expression))
  }

  private def completeModel(model: program.Model): program.Model = {
    val allVars = freeVars.map(v => v.toVal -> model.vars.getOrElse(v.toVal, simplestValue(v.getType))).toMap
    inox.Model(program)(allVars, model.chooses)
  }

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    config.convert(underlying.check(config),
      (model: Z3Model) => completeModel(underlying.extractModel(model)),
      underlying.extractUnsatAssumptions)

  override def checkAssumptions(config: Configuration)
                               (assumptions: Set[Expr]): config.Response[Model, Assumptions] =
    config.convert(underlying.checkAssumptions(config)(assumptions.map(underlying.toZ3Formula(_))),
      (model: Z3Model) => completeModel(underlying.extractModel(model)),
      underlying.extractUnsatAssumptions)
}
