/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package evaluators

import solvers._

import scala.collection.mutable.{Map => MutableMap}

trait SolvingEvaluator extends Evaluator {

  object optForallCache extends InoxOptionDef[MutableMap[program.trees.Forall, Boolean]] {
    val parser = { (_: String) => throw FatalError("Unparsable option \"bankOption\"") }
    val name = "bank-option"
    val description = "Evaluation bank shared between solver and evaluator"
    val usageRhs = ""
    def default = MutableMap.empty
  }

  def getSolver(opts: InoxOption[Any]*): Solver { val program: SolvingEvaluator.this.program.type }
}

trait SolvingEvalInterface {
  val program: Program
  import program._
  import program.trees._
  import program.symbols._

  val evaluator: DeterministicEvaluator with SolvingEvaluator { val program: SolvingEvalInterface.this.program.type }

  private val specCache: MutableMap[Expr, Expr] = MutableMap.empty
  private val forallCache: MutableMap[Forall, Expr] = MutableMap.empty

  def onSpecInvocation(specs: Expr): Expr = specCache.getOrElseUpdate(specs, {
    val Seq(free) = exprOps.variablesOf(specs).toSeq
    val timer = ctx.timers.evaluators.specs.start()

    val solver = evaluator.getSolver(evaluator.options.options.collect {
      case o @ InoxOption(opt, _) if opt == evaluator.optForallCache => o
    }.toSeq : _*)

    solver.assertCnstr(specs)
    val res = solver.check(model = true)
    timer.stop()

    res match {
      case solver.Model(model) =>
        valuateWithModel(model)(free.toVal)

      case _ =>
        throw new RuntimeException("Failed to evaluate specs " + specs.asString)
    }
  })

  def onForallInvocation(forall: Forall): Expr = {
    val cache = evaluator.options.findOption(evaluator.optForallCache).getOrElse {
      throw new RuntimeException("Couldn't find evaluator's forall cache")
    }
    
    BooleanLiteral(cache.getOrElse(forall, {
      val timer = ctx.timers.evaluators.forall.start()

      val solver = evaluator.getSolver(
        InoxOption(optSilentErrors)(true),
        InoxOption(optCheckModels)(false),
        InoxOption(evaluator.optForallCache)(cache)
      )

      solver.assertCnstr(Not(forall.body))
      val res = solver.check(model = true)
      timer.stop()

      res match {
        case solver.Unsat() =>
          cache(forall) = true
          true

        case solver.Model(model) =>
          cache(forall) = false
          evaluator.eval(Not(forall.body), model) match {
            case EvaluationResults.Successful(BooleanLiteral(true)) => false
            case _ => throw new RuntimeException("Forall model check failed")
          }

        case _ =>
          throw new RuntimeException("Failed to evaluate forall " + forall.asString)
      }
    }))
  }
}
