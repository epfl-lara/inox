/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers.z3

import z3.scala._

import Z3Native._
import solvers._
import utils.IncrementalSet

/** This is a rather direct mapping to Z3, where all functions are left uninterpreted.
 *  It reports the results as follows (based on the negation of the formula):
 *    - if Z3 reports UNSAT, it reports VALID
 *    - if Z3 reports SAT and the formula contained no function invocation, it returns INVALID with the counter-example/model
 *    - otherwise it returns UNKNOWN
 *  Results should come back very quickly.
 */
class UninterpretedZ3Solver(override val program: Program, override val context: Context)
                           (using protected val semantics: program.Semantics)
  extends AbstractSolver { self =>

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  type Trees = Expr
  type Model = program.Model

  import SolverResponses._

  val name = "z3-u"
  val description = "Uninterpreted Z3 Solver"

  private val underlying = new Underlying(program, context)

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

  def assertCnstr(expression: Expr): Unit = {
    freeVars ++= exprOps.variablesOf(expression)
    tryZ3(underlying.assertCnstr(underlying.toZ3Formula(expression)))
  }

  private def completeModel(model: program.Model): program.Model = {
    val allVars = freeVars.map(v => v.toVal -> model.vars.getOrElse(v.toVal, simplestValue(v.getType))).toMap
    inox.Model(program)(allVars, model.chooses)
  }

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    config.convert(
      // For some reasons, not specifying the type parameter T in tryZ3 causes some unexepected widening, which cause a typecheck error.
      tryZ3[config.Response[Z3Model, Set[Z3AST]]](underlying.check(config)).getOrElse(config.cast(Unknown)),
      (model: Z3Model) => completeModel(underlying.extractModel(model)),
      underlying.extractUnsatAssumptions)

  override def checkAssumptions(config: Configuration)
                               (assumptions: Set[Expr]): config.Response[Model, Assumptions] =
    config.convert(
      tryZ3(underlying.checkAssumptions(config)(assumptions.map(underlying.toZ3Formula(_))))
        .getOrElse(config.cast(Unknown)),
      (model: Z3Model) => completeModel(underlying.extractModel(model)),
      underlying.extractUnsatAssumptions)

  private class Underlying(override val program: self.program.type,
                           override val context: Context)
                          (using override val semantics: self.semantics.type)
    extends AbstractZ3Solver
}