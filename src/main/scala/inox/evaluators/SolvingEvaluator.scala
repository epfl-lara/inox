/* Copyright 2009-2018 EPFL, Lausanne */

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
  lazy val checkModels = options.findOptionOrDefault(optCheckModels)

  private val chooseCache: MutableMap[Choose, Expr] = MutableMap.empty

  // @nv: this has to be visible otherwise the compiler just sets it to `null`
  protected lazy val forallCache: MutableMap[Forall, Boolean] = {
    options.findOptionOrDefault(optForallCache)
  }

  def onChooseInvocation(choose: Choose): Expr = {
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of 'choose' expressions disabled @ ${choose.getPos}: $choose")
    }

    chooseCache.getOrElse(choose, {
      import scala.language.existentials
      val satRes = context.timers.evaluators.specs.run {
        val sf = semantics.getSolver
        val api = SimpleSolverAPI(sf)
        api.solveSAT(choose.pred)
      }

      import SolverResponses._

      val res = satRes match {
        case SatWithModel(model) =>
          if (model.chooses.nonEmpty && checkModels) {
            throw new RuntimeException("Cannot guarantee model for dependent choose " + choose.asString)
          } else try {
            model.vars.getOrElse(choose.res, simplestValue(choose.res.tpe, allowSolver = false))
          } catch {
            case _: NoSimpleValue => throw new RuntimeException("No simple value for choose " + choose.asString)
          }

        case _ =>
          throw new RuntimeException("Failed to evaluate choose " + choose.asString)
      }

      chooseCache(choose) = res
      res
    })
  }

  def onForallInvocation(forall: Forall): Expr = {
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of 'forall' expressions disabled @ ${forall.getPos}: $forall")
    }

    BooleanLiteral(forallCache.getOrElse(forall, {
      import scala.language.existentials
      val sf = context.timers.evaluators.forall.run {
        semantics.getSolver(context.withOpts(
          optSilentErrors(true),
          optCheckModels(false), // model is checked manually!! (see below)
          unrolling.optFeelingLucky(false),
          optForallCache(forallCache) // this makes sure we have an `optForallCache` set!
        ))
      }

      val api = SimpleSolverAPI(sf)

      // Check if one of the quantified types is empty, which makes the
      // forall true by definition.
      val quantifiesOverEmptyType: Boolean = {
        val vars = exprOps.variablesOf(forall.body)
        val emptyArgs = forall.params
          .filter(vd => !vars(vd.toVariable) && !(hasInstance(vd.tpe) contains true))
          .filter { vd =>
            import SolverResponses._
            val p = Variable.fresh("p", FunctionType(Seq(vd.getType), BooleanType()))
            val clause = Application(p, Seq(vd.toVariable))
            context.timers.evaluators.forall.run(api.solveSAT(clause)) match {
              case Unsat => true
              case SatWithModel(model) => eval(clause, model) match {
                case EvaluationResults.Successful(BooleanLiteral(true)) => false
                case _ => throw new RuntimeException("Forall model check failed")
              }
              case _ =>
                throw new RuntimeException("Failed to evaluate forall " + forall.asString)
            }
          }

        emptyArgs.nonEmpty
      }

      quantifiesOverEmptyType || {
        import SolverResponses._
        context.timers.evaluators.forall.run(api.solveSAT(Not(forall.body))) match {
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
      }
    }))
  }
}

