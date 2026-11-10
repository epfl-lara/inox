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

  private val choiceCache: MutableMap[Lambda, Expr] = MutableMap.empty

  // @nv: this has to be visible otherwise the compiler just sets it to `null`
  protected lazy val forallCache: MutableMap[Forall, Boolean] = {
    options.findOptionOrDefault(optForallCache)
  }

  private def hasRefinement(tpe: Type): Boolean =
    typeOps.exists { case _: RefinementType => true case _ => false } (tpe)

  /** The solvers that solve for chooses and foralls, which operate under the model of the
    * evaluation. */
  private def getSolver(chooses: Map[(Identifier, Seq[Type]), Expr])(using ctx: Context) =
    if (chooses.isEmpty) semantics.getSolver
    else semantics.getSolver(inox.Model(program)(Map.empty, chooses))

  /** The interpretations in `chooses` of the uninterpreted functions that `e` may call, directly or
    * through the functions and interpretations that it calls. The solvers only need to operate
    * under these, so that semantics whose solvers can't operate under a model still solve for the
    * chooses and foralls that call no uninterpreted function. */
  private def reachedChooses(e: Expr, chooses: Map[(Identifier, Seq[Type]), Expr]): Map[(Identifier, Seq[Type]), Expr] =
    if (chooses.isEmpty) chooses else {
      var functions = Set.empty[Identifier]
      var uninterpreted = Set.empty[Identifier]
      var todo = List.empty[Either[FunDef, Expr]]

      // Collects the functions and uninterpreted functions that are called, including in types
      object collector extends ConcreteSelfTreeTraverser(program.trees) {
        override def traverse(e: Expr): Unit = {
          e match {
            case fi: FunctionInvocation if !functions(fi.id) =>
              functions += fi.id
              todo ::= Left(getFunction(fi.id))
            case uc: UninterpretedCall if !uninterpreted(uc.id) =>
              uninterpreted += uc.id
              todo :::= chooses.toList.collect { case ((uc.id, _), body) => Right(body) }
            case _ =>
          }
          super.traverse(e)
        }
      }

      collector.traverse(e)
      while (todo.nonEmpty) {
        val next = todo.head
        todo = todo.tail
        next.fold(collector.traverse, collector.traverse)
      }
      chooses.filter { case ((id, _), _) => uninterpreted(id) }
    }

  /** Solves for a value of `res` that satisfies `pred`, whose free variables are bound to values.
    * The evaluators don't solve for the uninterpreted calls, which the model must interpret, but
    * languages that have their own choices (such as Stainless's `choose`) solve for them with this.
    * The values are cached outside of models, so that a choice always has the same value. */
  def solveFor(res: ValDef, pred: Expr, modelChooses: Map[(Identifier, Seq[Type]), Expr] = Map.empty): Expr = {
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of choices disabled @ ${pred.getPos}")
    }
    val key = Lambda(Seq(res), pred)

    // The predicate and the type of the result may call uninterpreted functions
    val chooses = reachedChooses(Forall(Seq(res), pred), modelChooses)

    // The results in a model only hold in that model
    (if (chooses.isEmpty) choiceCache.get(key) else None).getOrElse({
      import scala.language.existentials
      import SolverResponses._

      // Solves the predicate. Declaring the result makes the solver respect its type even when the
      // predicate doesn't mention it, as with a result of type `{ v: BigInt | v > 5 }` and predicate `true`,
      // but it also makes the solver look for a value of that type, which may never end: in Stainless's
      // ForestNothing2, the result's type is an ADT whose invariant only holds for infinite values.
      // So we only declare the result when its type has a refinement and no simple value.
      def solve(declareResult: Boolean): Option[Expr] = {
        val satRes = context.timers.evaluators.specs.run {
          val sf = getSolver(chooses)(using context)
          val solver = sf.getNewSolver()
          try {
            if (declareResult) solver.declare(res)
            solver.assertCnstr(pred)
            solver.check(Model)
          } finally {
            sf.reclaim(solver)
          }
        }

        satRes match {
          case SatWithModel(model) =>
            if ((model.chooses.keySet -- chooses.keySet).nonEmpty && checkModels) {
              throw new RuntimeException("Cannot guarantee model for dependent call " + key.asString)
            }
            model.vars.get(res)

          case _ =>
            throw new RuntimeException("Failed to evaluate " + key.asString)
        }
      }

      val value = solve(declareResult = false).getOrElse {
        try {
          simplestValue(res.tpe, allowSolver = false)
        } catch {
          case _: NoSimpleValue if hasRefinement(res.tpe) => solve(declareResult = true).getOrElse {
            throw new RuntimeException("No simple value for " + key.asString)
          }
          case _: NoSimpleValue =>
            throw new RuntimeException("No simple value for " + key.asString)
        }
      }

      if (chooses.isEmpty) choiceCache(key) = value
      value
    })
  }

  def onForallInvocation(forall: Forall, modelChooses: Map[(Identifier, Seq[Type]), Expr] = Map.empty): Expr = {
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of 'forall' expressions disabled @ ${forall.getPos}: $forall")
    }
    val chooses = reachedChooses(forall, modelChooses)

    // The results in a model only hold in that model
    BooleanLiteral((if (chooses.isEmpty) forallCache.get(forall) else None).getOrElse({
      import scala.language.existentials
      val sf = context.timers.evaluators.forall.run {
        getSolver(chooses)(using context.withOpts(
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
            if (chooses.isEmpty) forallCache(forall) = true
            true

          case SatWithModel(model) =>
            if (chooses.isEmpty) forallCache(forall) = false
            eval(Not(forall.body), inox.Model(program)(model.vars, chooses ++ model.chooses)) match {
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

