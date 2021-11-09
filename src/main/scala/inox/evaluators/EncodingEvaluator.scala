/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package evaluators

class EncodingEvaluator(override val program: Program, override val context: Context)
                       (val encoder: transformers.ProgramTransformer { val sourceProgram: program.type })
                       (val underlying: DeterministicEvaluator { val program: encoder.targetProgram.type })
  extends DeterministicEvaluator { self =>
  import program.trees._

  def this(program: Program,
           encoder: transformers.ProgramTransformer { val sourceProgram: program.type },
           underlying: DeterministicEvaluator { val program: encoder.targetProgram.type }) =
    this(program, underlying.context)(encoder)(underlying)

  def eval(expr: Expr, model: program.Model): EvaluationResult = {
    val res = underlying.eval(encoder.encode(expr), model.encode(encoder))

    res match {
      case EvaluationResults.Successful(v) => EvaluationResults.Successful(encoder.decode(v))
      case EvaluationResults.RuntimeError(msg) => EvaluationResults.RuntimeError(msg)
      case EvaluationResults.EvaluatorError(msg) => EvaluationResults.EvaluatorError(msg)
    }
  }
}

object EncodingEvaluator {
  def apply(p: Program)
           (enc: transformers.ProgramTransformer { val sourceProgram: p.type })
           (ev: DeterministicEvaluator { val program: enc.targetProgram.type }) = {
    class Impl(override val program: p.type,
               override val encoder: enc.type,
               override val underlying: ev.type) extends EncodingEvaluator(program, encoder, underlying)
    new Impl(p, enc, ev)
  }
}