/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package evaluators

object optMaxCalls extends IntOptionDef("maxcalls", 50000, "<PosInt> | -1 (for unbounded")

trait ContextualEvaluator extends Evaluator {
  import program._
  import program.trees._

  lazy val maxSteps: Int = options.findOptionOrDefault(optMaxCalls)

  trait RecContext[RC <: RecContext[RC]] {
    def mappings: Map[ValDef, Expr]
    def newVars(news: Map[ValDef, Expr]): RC
    def withNewVar(vd: ValDef, expr: Expr): RC = newVars(mappings + (vd -> expr))
    def withNewVars(news: Map[ValDef, Expr]): RC = newVars(mappings ++ news)
  }

  case class DefaultRecContext(mappings: Map[ValDef, Expr]) extends RecContext[DefaultRecContext] {
    def newVars(news: Map[ValDef, Expr]) = copy(mappings = news)
  }

  class GlobalContext(val maxSteps: Int) {
    var stepsLeft = maxSteps
  }

  type RC <: RecContext[RC]
  type GC <: GlobalContext

  def initRC(mappings: Map[ValDef, Expr]): RC
  def initGC: GC

  case class EvalError(msg: String) extends Exception {
    override def getMessage = msg + Option(super.getMessage).map("\n" + _).getOrElse("")
  }
  case class RuntimeError(msg: String) extends Exception
  case class QuantificationError(msg: String) extends Exception

  def eval(ex: Expr, model: Map[ValDef, Expr]) = {
    try {
      ctx.timers.evaluators.recursive.runtime.start()
      EvaluationResults.Successful(e(ex)(initRC(model), initGC))
    } catch {
      case EvalError(msg) =>
        EvaluationResults.EvaluatorError(msg)
      case so: StackOverflowError =>
        EvaluationResults.RuntimeError("Stack overflow")
      case e @ RuntimeError(msg) =>
        EvaluationResults.RuntimeError(msg)
      case jre: java.lang.RuntimeException =>
        EvaluationResults.RuntimeError(jre.getMessage)
    } finally {
      ctx.timers.evaluators.recursive.runtime.stop()
    }
  }

  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): Value

  def typeErrorMsg(tree: Expr, expected: Type): String = s"Type error : expected ${expected.asString}, found ${tree.asString} of type ${tree.getType}."
}

trait HasDefaultRecContext extends ContextualEvaluator {
  import program.trees._
  type RC = DefaultRecContext
  def initRC(mappings: Map[ValDef, Expr]) = DefaultRecContext(mappings)
}

trait HasDefaultGlobalContext extends ContextualEvaluator {
  type GC = GlobalContext
  def initGC = new GlobalContext(maxSteps)
}

