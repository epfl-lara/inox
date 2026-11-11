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

  /** The interpretations in `interpretations` of the uninterpreted functions that `e` may call,
    * directly or through the functions and interpretations that it calls. The solvers only need to
    * operate under these, so that semantics whose solvers can't operate under a model still solve
    * for the foralls that call no uninterpreted function. */
  protected def reachedInterpretations(e: Expr, interpretations: Map[(Identifier, Seq[Type]), Expr]): Map[(Identifier, Seq[Type]), Expr] =
    if (interpretations.isEmpty) interpretations else {
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
              todo :::= interpretations.toList.collect { case ((uc.id, _), body) => Right(body) }
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
      interpretations.filter { case ((id, _), _) => uninterpreted(id) }
    }

  def onForallInvocation(forall: Forall, modelInterpretations: Map[(Identifier, Seq[Type]), Expr] = Map.empty): Expr = {
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of 'forall' expressions disabled @ ${forall.getPos}: $forall")
    }
    val interpretations = reachedInterpretations(forall, modelInterpretations)

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
}

