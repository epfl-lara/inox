/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package evaluators

import solvers._

import scala.collection.mutable.{Map => MutableMap}

trait SolvingEvaluator extends Evaluator {
  import program._
  import program.trees._
  import program.symbols._

  object optForallCache extends InoxOptionDef[MutableMap[program.trees.Forall, Boolean]] {
    val parser = { (_: String) => throw FatalError("Unparsable option \"bankOption\"") }
    val name = "bank-option"
    val description = "Evaluation bank shared between solver and evaluator"
    val usageRhs = ""
    def default = MutableMap.empty
  }

  def getSolver(opts: InoxOption[Any]*): SolverFactory { val program: SolvingEvaluator.this.program.type }

  private val specCache: MutableMap[Expr, Expr] = MutableMap.empty
  private val forallCache: MutableMap[Forall, Expr] = MutableMap.empty

  def onSpecInvocation(specs: Lambda): Expr = specCache.getOrElseUpdate(specs, {
    val Lambda(Seq(vd), body) = specs
    val timer = ctx.timers.evaluators.specs.start()

    val sf = getSolver(options.options.collect {
      case o @ InoxOption(opt, _) if opt == optForallCache => o
    }.toSeq : _*)

    import SolverResponses._

    val api = SimpleSolverAPI(sf)
    val res = api.solveSAT(body)
    timer.stop()

    res match {
      case SatWithModel(model) =>
        valuateWithModel(model)(vd)

      case _ =>
        throw new RuntimeException("Failed to evaluate specs " + specs.asString)
    }
  })

  def onForallInvocation(forall: Forall): Expr = {
    val cache = options.findOption(optForallCache).getOrElse {
      throw new RuntimeException("Couldn't find evaluator's forall cache")
    }
    
    BooleanLiteral(cache.getOrElse(forall, {
      val timer = ctx.timers.evaluators.forall.start()

      val sf = getSolver(
        InoxOption(optSilentErrors)(true),
        InoxOption(optCheckModels)(false),
        InoxOption(optForallCache)(cache)
      )

      import SolverResponses._

      val api = SimpleSolverAPI(sf)
      val res = api.solveSAT(Not(forall.body))
      timer.stop()

      res match {
        case Unsat =>
          cache(forall) = true
          true

        case SatWithModel(model) =>
          cache(forall) = false
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

