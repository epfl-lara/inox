/* Copyright 2009-2024 EPFL, Lausanne */

package inox
package solvers
package evaluating

import inox.solvers.SolverResponses.CheckConfiguration

import inox.solvers.SolverResponses.Configuration
import scala.collection.mutable.ListBuffer
import inox.utils.IncrementalSeq
import inox.solvers.smtlib.SMTLIBSolver
import scala.collection.immutable.LazyList.cons
import inox.utils.IncrementalBijection
import inox.evaluators.DeterministicEvaluator
import inox.evaluators.EvaluationResults.Successful
import inox.evaluators.EvaluationResults.RuntimeError
import inox.evaluators.EvaluationResults.EvaluatorError

object EvaluatingSolver:

end EvaluatingSolver

/**
  * A solver that evaluates ground constraints using the internal program
  * evaluator. Non-ground constriants will return [[Unknown]]. 
  */
abstract class EvaluatingSolver(override val program: Program,
   override val context: Context)
  // Alias for `program`, as there are some places where `program` is shadowed.
  (val prog: program.type)
  (val enc: transformers.ProgramTransformer {val sourceProgram: program.type})
  (val programEncoder: transformers.ProgramTransformer {
    val sourceProgram: program.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  })
  (using val semantics: program.Semantics,
         val semanticsProvider: SemanticsProvider {val trees: enc.targetProgram.trees.type})
  extends Solver:

  /* Internal imports, types, and aliases */

  protected final val s: programEncoder.sourceProgram.trees.type = programEncoder.sourceProgram.trees
  protected final val t: programEncoder.targetProgram.trees.type = programEncoder.targetProgram.trees
  protected final val targetProgram: programEncoder.targetProgram.type = programEncoder.targetProgram

  type Source  = s.Expr
  type Encoded = t.Expr

  import targetProgram._
  import targetProgram.trees._
  import targetProgram.symbols.{given, _}

  protected val reporter = context.reporter

  protected val encoder = enc

  /* Interface */

  /**
    * Checks whether the given set of assumptions is satisfiable together with
    * the current state. Does not permanently add them to the constraint set,
    * unlike [[assertCnstr]] + [[check]].
    *
    * @param config expected response configuration
    * @param assumptions set of assumptions to check
    * @return a response containing satisfiability result, and a model if the
    * config requires it and one is available
    */
  override def checkAssumptions(config: Configuration)(assumptions: Set[Source]): config.Response[Model, Assumptions] = 
    checkAssumptions_(config)(assumptions)

  override def declare(vd: program.trees.ValDef): Unit = 
    val evd = encode(vd)

    context.timers.solvers.declare.sanity.run:
      assert(evd.getType.isTyped)

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

  override def interrupt(): Unit = 
    abort = true

  override def reset(): Unit = 
    abort = false
    failures.clear()
    constraints.reset()

  override def push(): Unit = 
    constraints.push()

  override def pop(): Unit = 
    constraints.pop()

  override def free(): Unit = 
    failures.clear()
    constraints.clear()
    context.interruptManager.unregisterForInterrupts(this)

  /**
    * Checks the satisfiability of the currently asserted set of constraints.
    *
    * @param config expected response configuration
    * @return a response containing satisfiability result, and a model if the
    * config requires it and one is available
    */
  override def check(config: CheckConfiguration): config.Response[Model, Assumptions] = 
    checkAssumptions(config)(Set.empty)

  /**
    * Asserts a constraint to the solver. A call to [[check]] checks the
    * satisfiability of the conjunction of all asserted constraints.
    *
    * @param expression constraint to assert
    */
  override def assertCnstr(expression: Source): Unit = 
    constraints += expression

  override def name: String = "eval"

  /* Internal state */

  // options
  val silentErrors: Boolean = context.options.findOptionOrDefault(optSilentErrors)

  /**
    * List of exceptions caught during this run. Thrown when the solver is asked
    * to check constraints next. 
    */
  protected val failures: ListBuffer[Throwable] = new ListBuffer

  /**
    * Whether the solver has been externally interrupted. See [[interrupt]].
    */
  private var abort: Boolean = false

  /**
    * Stack of constraints to check.
    */
  protected val constraints: IncrementalSeq[Source] = new IncrementalSeq()

  protected val evaluator: DeterministicEvaluator {val program: targetProgram.type} = targetProgram.getEvaluator(context)

  /* Translation of expressions */

  // encoding and decoding trees

  protected final def encode(vd: s.ValDef): t.ValDef = programEncoder.encode(vd)
  protected final def decode(vd: t.ValDef): s.ValDef = programEncoder.decode(vd)

  protected final def encode(v: s.Variable): t.Variable = programEncoder.encode(v)
  protected final def decode(v: t.Variable): s.Variable = programEncoder.decode(v)

  protected final def encode(e: s.Expr): t.Expr = programEncoder.encode(e)
  protected final def decode(e: t.Expr): s.Expr = programEncoder.decode(e)

  protected final def encode(tpe: s.Type): t.Type = programEncoder.encode(tpe)
  protected final def decode(tpe: t.Type): s.Type = programEncoder.decode(tpe)


  /* Checking satisfiability */

  case class RuntimeErrorException(message: String) extends InternalSolverError("Runtime error during evaluation: " + message)
  case class EvaluatorErrorException(message: String) extends InternalSolverError("Internal evaluator error during evaluation: " + message)
  case class TypeMismatchException(expected: Type, found: Type) extends InternalSolverError(s"Type mismatch during evaluation: Expected $expected, found $found.")

  private def isGround(e: Encoded): Boolean = 
    exprOps.variablesOf(e).isEmpty

  private def evaluate(e: Encoded): Boolean =
    require(e.getType == BooleanType())
    evaluator.eval(e) match
      case Successful(BooleanLiteral(b)) => b
      case Successful(value) => throw TypeMismatchException(BooleanType(), value.getType)
      case RuntimeError(message) => throw RuntimeErrorException(message)
      case EvaluatorError(message) => throw EvaluatorErrorException(message)
    

  private val emptyModel: Model = inox.Model(program)(Map.empty, Map.empty)

  private def checkAssumptions_(config: Configuration)(assumptions: Set[Source]): config.Response[Model, Assumptions] = 
    import SolverResponses.* 

    context.timers.solvers.evaluating.run(scala.util.Try({
      
      val encodedAssumptions = (assumptions ++ constraints).map(encode)  

      // do we even support these assumptions?
      if (encodedAssumptions.exists(!isGround(_))) then
        config.cast(Unknown)
      else 
        // attempt to solve
        val res = 
          encodedAssumptions
            .to(LazyList)
            .map(evaluate)
            .forall(identity) // early return conjunction
        
        if res then           // all true, => valid ground truth
          config.cast(SatWithModel(emptyModel))
        else                  // some false, => conjunction invalid
          config.cast(Unsat)

    }).recover {
      case e @ (_: InternalSolverError | _: Unsupported) =>
        if (reporter.isDebugEnabled) reporter.debug(e)
        else if (!silentErrors && !abort) reporter.error(e.getMessage)
        config.cast(Unknown)
    }.get)
    