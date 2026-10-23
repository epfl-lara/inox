/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import evaluators._
import transformers._

package object theories {

  case class TheoryException(msg: String)
    extends Unsupported(s"Theory encoding failed: $msg")

  // Z3 supports all the Inox theories natively. Strings are encoded as sequences of 16-bit
  // bit-vectors by the native API, and the SMT-LIB target restricts the string alphabet to
  // the BMP (see `Z3Target`), so that solver characters coincide with Inox characters.
  def Z3(p: Program): ProgramTransformer {
    val sourceProgram: p.type
    val targetProgram: Program { val trees: p.trees.type }
  } = ProgramEncoder.empty(p)

  def CVC(enc: ProgramTransformer)
         (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }): ProgramTransformer {
    val sourceProgram: enc.targetProgram.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  } = {
    // Strings are kept as SMT-LIB strings: cvc5 restricts its alphabet to the BMP (see
    // `CVC5Solver`), and CVC4 models with characters outside of the BMP are rejected
    // when they are translated back (see `SMTLIBTarget.fromSMT`).
    val bagEncoder = BagEncoder(enc)(ev)
    val mapMergeEncoder = MapMergeEncoder(bagEncoder.targetProgram)
    bagEncoder `andThen` mapMergeEncoder
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

