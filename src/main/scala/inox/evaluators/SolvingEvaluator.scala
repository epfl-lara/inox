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

  // @nv: this has to be visible otherwise the compiler just sets it to `null`
  protected lazy val forallCache: MutableMap[Forall, Boolean] = {
    options.findOptionOrDefault(optForallCache)
  }

  /** The solvers that evaluate foralls, which operate under the model of the evaluation. */
  protected def getSolver(interpretations: Map[(Identifier, Seq[Type]), Expr])(using ctx: Context) =
    if (interpretations.isEmpty) semantics.getSolver
    else semantics.getSolver(inox.Model(program)(Map.empty, interpretations))

  def onForallInvocation(forall: Forall, modelInterpretations: Map[(Identifier, Seq[Type]), Expr] = Map.empty): Expr = {
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of 'forall' expressions disabled @ ${forall.getPos}: $forall")
    }
    val interpretations = transitiveInterpretations(forall, modelInterpretations)

    // The results in a model only hold in that model
    BooleanLiteral((if (interpretations.isEmpty) forallCache.get(forall) else None).getOrElse({
      import scala.language.existentials
      val sf = context.timers.evaluators.forall.run {
        getSolver(interpretations)(using context.withOpts(
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
            if (interpretations.isEmpty) forallCache(forall) = true
            true

          case SatWithModel(model) =>
            if (interpretations.isEmpty) forallCache(forall) = false
            eval(Not(forall.body), inox.Model(program)(model.vars, interpretations ++ model.interpretations)) match {
              case EvaluationResults.Successful(BooleanLiteral(true)) => false
              case _ => throw new RuntimeException("Forall model check failed")
            }

          case _ =>
            throw new RuntimeException("Failed to evaluate forall " + forall.asString)
        }
      }
    }))
  }

  private val lambdaComparisonCache: MutableMap[(Lambda, Lambda), LambdaComparison] = MutableMap.empty

  /** Compares the closed lambdas `l1` and `l2` with a solver, under extensional function equality
    * (see [[solvers.unrolling.optFunctionEquality]]), when the inputs that the evaluator tries don't
    * tell them apart.
    *
    * The answer is [[LambdaComparison.Equal]] when the solver proves that they are equal (an UNSAT
    * answer, which is sound), and [[LambdaComparison.Input]] with an input on which the solver finds
    * that they differ. The caller then confirms that they differ on it by evaluating them, since
    * the solver's models aren't checked. Quantifiers must be evaluated (see [[optEvalQuantifiers]]),
    * as these queries use the same solvers. */
  def onLambdaComparison(l1: Lambda, l2: Lambda,
      modelInterpretations: Map[(Identifier, Seq[Type]), Expr] = Map.empty): LambdaComparison = {
    if (!evalQuantifiers) LambdaComparison.Unknown else {
      val interpretations = transitiveInterpretations(Tuple(Seq(l1, l2)), modelInterpretations)
      // The results in a model only hold in that model
      val cached = if (interpretations.isEmpty) lambdaComparisonCache.get(l1 -> l2) else None
      cached.getOrElse {
        import SolverResponses._
        val api = SimpleSolverAPI(context.timers.evaluators.forall.run {
          getSolver(interpretations)(using context.withOpts(
            optSilentErrors(true),
            optCheckModels(false),
            unrolling.optFeelingLucky(false),
            optForallCache(forallCache)
          ))
        })

        // a query that the solver rejects or fails on decides nothing
        def solve(expr: Expr) = try {
          context.timers.evaluators.forall.run(api.solveSAT(expr))
        } catch {
          case scala.util.control.NonFatal(_) => Unknown
        }

        val res = solve(Not(Equals(l1, l2))) match {
          case Unsat => LambdaComparison.Equal
          case _ =>
            val args = l1.params.map(vd => Variable.fresh(vd.id.name, vd.getType))
            solve(Not(Equals(Application(l1, args), Application(l2, args)))) match {
              case SatWithModel(model) =>
                val values = args.map(a => model.vars.get(a.toVal))
                if (values.forall(_.isDefined)) LambdaComparison.Input(values.flatten)
                else LambdaComparison.Unknown
              case _ => LambdaComparison.Unknown
            }
        }
        // an unknown answer may come from an interrupt or a timeout
        if (interpretations.isEmpty && res != LambdaComparison.Unknown) lambdaComparisonCache(l1 -> l2) = res
        res
      }
    }
  }

  /** The result of [[onLambdaComparison]]. */
  enum LambdaComparison {
    /** The lambdas agree on every input. */
    case Equal
    /** An input on which the lambdas may differ. */
    case Input(args: Seq[Expr])
    /** The solver can't tell. */
    case Unknown
  }
}
