/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import evaluators._

package object theories {

  trait Z3Theories { self: unrolling.AbstractUnrollingSolver =>
    val theories = StringEncoder(self.encoder.targetProgram)
  }

  trait CVC4Theories { self: unrolling.AbstractUnrollingSolver =>
    val theories = BagEncoder(self.encoder, self.options)(self.evaluator)
  }

  trait PrincessTheories { self: unrolling.AbstractUnrollingSolver =>
    val stringEncoder = StringEncoder(self.encoder.targetProgram)

    // @nv: needed to avoid existential in bagEncoder's type
    val encoderAndString = self.encoder andThen stringEncoder
    val bagEncoder = BagEncoder(encoderAndString, self.options)(self.evaluator)

    // @nv: needed to avoid existential in setEncoder's type
    val encoderAndBag = encoderAndString andThen bagEncoder
    val setEncoder = SetEncoder(encoderAndBag, self.options)(self.evaluator)

    // @nv: needed to avoid existential in theories' type
    val stringAndBag = stringEncoder andThen bagEncoder
    val theories = stringAndBag andThen setEncoder
  }

  object ReverseEvaluator {
    def apply(enc: ast.ProgramTransformer, opts: Options)
             (ev: DeterministicEvaluator { val program: enc.sourceProgram.type }):
             DeterministicEvaluator { val program: enc.targetProgram.type } = new {
      val program: enc.targetProgram.type = enc.targetProgram
      val options = opts
    } with DeterministicEvaluator {
      import program.trees._
      import EvaluationResults._

      def eval(e: Expr, model: Map[ValDef, Expr]): EvaluationResult = {
        ev.eval(enc.decode(e), model.map {
          case (vd, value) => enc.decode(vd) -> enc.decode(value)
        }) match {
          case Successful(value) => Successful(enc.encode(value))
          case RuntimeError(message) => RuntimeError(message)
          case EvaluatorError(message) => EvaluatorError(message)
        }
      }
    }
  }
}

