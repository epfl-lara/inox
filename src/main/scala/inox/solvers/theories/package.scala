/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import evaluators._

package object theories {

  def Z3(p: Program): ast.ProgramTransformer {
    val sourceProgram: p.type
    val targetProgram: Program { val trees: p.trees.type }
  } = ASCIIStringEncoder(p)

  def CVC4(enc: ast.ProgramTransformer)
          (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }): ast.ProgramTransformer {
    val sourceProgram: enc.targetProgram.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  } = {
    val stringEncoder = ASCIIStringEncoder(enc.targetProgram)
    val encAndString = enc andThen stringEncoder
    val bagEncoder = BagEncoder(encAndString)(ev)
    stringEncoder andThen bagEncoder
  }

  def Princess(enc: ast.ProgramTransformer)
              (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }): ast.ProgramTransformer {
    val sourceProgram: enc.targetProgram.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  } = {
    val stringEncoder = StringEncoder(enc.targetProgram)

    val encAndString = enc andThen stringEncoder
    val bagEncoder = BagEncoder(encAndString)(ev)

    val setEncoder = SetEncoder(bagEncoder.targetProgram)

    val bvEncoder = BitvectorEncoder(setEncoder.targetProgram)

    val realEncoder = RealEncoder(bvEncoder.targetProgram)

    // @nv: Required due to limitations in scalac existential types
    val e1 = stringEncoder andThen bagEncoder
    val e2 = e1 andThen setEncoder
    val e3 = e2 andThen bvEncoder
    e3 andThen realEncoder
  }

  object ReverseEvaluator {
    def apply(enc: ast.ProgramTransformer)
             (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }):
             DeterministicEvaluator { val program: enc.targetProgram.type } = new {
      val program: enc.targetProgram.type = enc.targetProgram
      val options = ev.options
    } with DeterministicEvaluator {
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
  }
}

