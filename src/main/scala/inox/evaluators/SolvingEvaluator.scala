/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package evaluators

import solvers._
import solvers.combinators._

import scala.collection.mutable.{Map => MutableMap}

trait SolvingEvaluator extends Evaluator { self =>
  import context._
  import program._
  import program.trees._
  import program.symbols._

  protected implicit val semantics: program.Semantics

  private object optForallCache extends OptionDef[MutableMap[Forall, Boolean]] {
    val parser = { (_: String) => throw FatalError("Unparsable option \"forallCache\"") }
    val name = "forall-cache"
    val usageRhs = "No possible usage"
    def default = MutableMap.empty
  }

  lazy val evalQuantifiers = options.findOptionOrDefault(optEvalQuantifiers)

  private val chooseCache: MutableMap[Choose, Expr] = MutableMap.empty

  // @nv: this has to be visible otherwise the compiler just sets it to `null`
  protected lazy val forallCache: MutableMap[Forall, Boolean] = {
    options.findOptionOrDefault(optForallCache)
  }

  def onChooseInvocation(choose: Choose): Expr = {
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of 'choose' expressions disabled @ ${choose.getPos}")
    }

    chooseCache.getOrElseUpdate(choose, {
      import scala.language.existentials
      val res = context.timers.evaluators.specs.run {
        val sf = semantics.getSolver
        val api = SimpleSolverAPI(sf)
        api.solveSAT(choose.pred)
      }

      import SolverResponses._

      res match {
        case SatWithModel(model) =>
          try {
            model.vars.getOrElse(choose.res, simplestValue(choose.res.tpe, allowSolver = false))
          } catch {
            case _: NoSimpleValue => throw new RuntimeException("No simple value for choose " + choose.asString)
          }

        case _ =>
          throw new RuntimeException("Failed to evaluate choose " + choose.asString)
      }
    })
  }

  def onForallInvocation(forall: Forall): Expr = {
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of 'forall' expressions disabled @ ${forall.getPos}")
    }

    BooleanLiteral(forallCache.getOrElse(forall, {
      import scala.language.existentials
      val res = context.timers.evaluators.forall.run {
        val sf = semantics.getSolver(context.withOpts(
          optSilentErrors(true),
          optCheckModels(false), // model is checked manually!! (see below)
          unrolling.optFeelingLucky(false),
          optForallCache(forallCache) // this makes sure we have an `optForallCache` set!
        ))

        val api = SimpleSolverAPI(sf)
        api.solveSAT(Not(forall.body))
      }

      import SolverResponses._

      res match {
        case Unsat =>
          forallCache(forall) = true
          true

        case SatWithModel(model) =>
          forallCache(forall) = false
          eval(Not(forall.body), model) match {
            case EvaluationResults.Successful(BooleanLiteral(true)) => false
            case _ => throw new RuntimeException("Forall model check failed")
          }

        case _ =>
          throw new RuntimeException("Failed to evaluate forall " + forall.asString)
      }
    }))
  }
}

