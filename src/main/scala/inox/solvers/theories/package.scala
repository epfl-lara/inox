/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import evaluators._
import transformers._

package object theories {

  case class TheoryException(msg: String)
    extends Unsupported(s"Theory encoding failed: $msg")

  def Z3(p: Program): ProgramTransformer {
    val sourceProgram: p.type
    val targetProgram: Program { val trees: p.trees.type }
  } = ASCIIStringEncoder(p)

  def CVC(enc: ProgramTransformer)
         (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }): ProgramTransformer {
    val sourceProgram: enc.targetProgram.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  } = {
    val stringEncoder = ASCIIStringEncoder(enc.targetProgram)
    val encAndString = enc `andThen` stringEncoder
    val bagEncoder = BagEncoder(encAndString)(ev)
    val mapMergeEncoder = MapMergeEncoder(bagEncoder.targetProgram)

    val e1 = stringEncoder `andThen` bagEncoder
    e1 `andThen` mapMergeEncoder
  }

  def Princess(enc: ProgramTransformer)
              (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }): ProgramTransformer {
    val sourceProgram: enc.targetProgram.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  } = {
    val stringEncoder = StringEncoder(enc.targetProgram)

    val encAndString = enc `andThen` stringEncoder
    val bagEncoder = BagEncoder(encAndString)(ev)
    val mapMergeEncoder = MapMergeEncoder(bagEncoder.targetProgram)

    val setEncoder = SetEncoder(mapMergeEncoder.targetProgram)

    val realEncoder = RealEncoder(setEncoder.targetProgram)

    // @nv: Required due to limitations in scalac existential types
    val e1 = stringEncoder `andThen` bagEncoder
    val e2 = e1 `andThen` mapMergeEncoder
    val e3 = e2 `andThen` setEncoder
    e3 `andThen` realEncoder
  }

  object ReverseEvaluator {
    def apply(enc: ProgramTransformer)
             (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }):
             DeterministicEvaluator { val program: enc.targetProgram.type } = {
      class ReverseEvaluatorImpl(override val program: enc.targetProgram.type,
                                 override val context: inox.Context) extends DeterministicEvaluator {
        import program.trees._
        import EvaluationResults._

        def eval(e: Expr, model: program.Model): EvaluationResult = {
          ev.eval(enc.decode(e), model.encode(enc.reverse)) match {
            case Successful(value) => Successful(enc.encode(value))
            case RuntimeError(message) => RuntimeError(message)
            case EvaluatorError(message) => EvaluatorError(message)
          }
        }
      }
      new ReverseEvaluatorImpl(enc.targetProgram, ev.context)
    }
  }
}

