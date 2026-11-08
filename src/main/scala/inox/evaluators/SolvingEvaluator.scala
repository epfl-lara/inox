/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package evaluators

import solvers._
import solvers.combinators._

import scala.collection.mutable.{Map => MutableMap}

trait SolvingEvaluator extends Evaluator { self =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  protected val semantics: program.Semantics
  given givenSemantics: semantics.type = semantics

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

  private def hasRefinement(tpe: Type): Boolean =
    typeOps.exists { case _: RefinementType => true case _ => false } (tpe)

  def onChooseInvocation(choose: Choose): Expr = {
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of 'choose' expressions disabled @ ${choose.getPos}: $choose")
    }

    chooseCache.getOrElse(choose, {
      import scala.language.existentials
      import SolverResponses._

      // Solves the choose's predicate. Declaring the result makes the solver respect its type
      // even when the predicate doesn't mention it, as with `choose((x: { v: BigInt | v > 5 }) => true)`,
      // but it also makes the solver look for a value of that type, which may never end: in Stainless's
      // ForestNothing2, the result's type is an ADT whose invariant only holds for infinite values.
      // So we only declare the result when its type has a refinement and no simple value.
      def solve(declareResult: Boolean): Option[Expr] = {
        val satRes = context.timers.evaluators.specs.run {
          val sf = semantics.getSolver
          val solver = sf.getNewSolver()
          try {
            if (declareResult) solver.declare(choose.res)
            solver.assertCnstr(choose.pred)
            solver.check(Model)
          } finally {
            sf.reclaim(solver)
          }
        }

        satRes match {
          case SatWithModel(model) =>
            if (model.chooses.nonEmpty && checkModels) {
              throw new RuntimeException("Cannot guarantee model for dependent choose " + choose.asString)
            }
            model.vars.get(choose.res)

          case _ =>
            throw new RuntimeException("Failed to evaluate choose " + choose.asString)
        }
      }

      val res = solve(declareResult = false).getOrElse {
        try {
          simplestValue(choose.res.tpe, allowSolver = false)
        } catch {
          case _: NoSimpleValue if hasRefinement(choose.res.tpe) => solve(declareResult = true).getOrElse {
            throw new RuntimeException("No simple value for choose " + choose.asString)
          }
          case _: NoSimpleValue =>
            throw new RuntimeException("No simple value for choose " + choose.asString)
        }
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
        semantics.getSolver(using context.withOpts(
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
        // the solver rejects quantifiers that compare functions without function equality, eg.
        // over model values that do (see [[solvers.unrolling.optFunctionEquality]])
        val res = try {
          context.timers.evaluators.forall.run(api.solveSAT(Not(forall.body)))
        } catch {
          case e: ast.TypeOps#TypeErrorException => throw new RuntimeException(e.getMessage)
        }
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
      }
    }))
  }
}

