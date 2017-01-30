/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package evaluators

object optMaxCalls extends IntOptionDef("maxcalls", 50000, "<PosInt> | -1 (unbounded)")

trait ContextualEvaluator extends Evaluator {
  import program._
  import program.trees._

  lazy val maxSteps: Int = options.findOptionOrDefault(optMaxCalls)

  trait RecContext[RC <: RecContext[RC]] {
    def tps: Seq[Type]
    def mappings: Map[ValDef, Expr]
    def chooses: Map[(Identifier, Seq[Type]), Expr]

    def newTypes(tps: Seq[Type]): RC

    def newVars(news: Map[ValDef, Expr]): RC
    def withNewVar(vd: ValDef, expr: Expr): RC = newVars(mappings + (vd -> expr))
    def withNewVars(news: Map[ValDef, Expr]): RC = newVars(mappings ++ news)

    def newChooses(news: Map[(Identifier, Seq[Type]), Expr]): RC
    def getChoose(id: Identifier): Option[Expr] = chooses.get(id -> tps)
    def withoutChoose(id: Identifier) = newChooses(chooses - (id -> tps))
  }

  case class DefaultRecContext(
    tps: Seq[Type],
    mappings: Map[ValDef, Expr],
    chooses: Map[(Identifier, Seq[Type]), Expr]
  ) extends RecContext[DefaultRecContext] {
    def newTypes(tps: Seq[Type]) = copy(tps = tps)
    def newVars(news: Map[ValDef, Expr]) = copy(mappings = news)
    def newChooses(news: Map[(Identifier, Seq[Type]), Expr]) = copy(chooses = news)
  }

  class GlobalContext(val maxSteps: Int) {
    var stepsLeft = maxSteps
  }

  type RC <: RecContext[RC]
  type GC <: GlobalContext

  def initRC(model: program.Model): RC
  def initGC: GC

  case class EvalError(msg: String) extends Exception {
    override def getMessage = msg + Option(super.getMessage).map("\n" + _).getOrElse("")
  }
  case class RuntimeError(msg: String) extends Exception
  case class QuantificationError(msg: String) extends Exception

  def eval(ex: Expr, model: program.Model) = {
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
  def initRC(model: program.Model) = DefaultRecContext(Seq.empty, model.vars, model.chooses)
}

trait HasDefaultGlobalContext extends ContextualEvaluator {
  type GC = GlobalContext
  def initGC = new GlobalContext(maxSteps)
}

