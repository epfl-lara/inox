/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import evaluators._

package object theories {

  trait Z3Theories { self: unrolling.AbstractUnrollingSolver =>
    lazy val theories = StringEncoder(self.fullEncoder.targetProgram)
  }

  trait CVC4Theories { self: unrolling.AbstractUnrollingSolver =>
    lazy val theories = BagEncoder(self.fullEncoder)(self.evaluator)
  }

  trait PrincessTheories { self: unrolling.AbstractUnrollingSolver =>
    lazy val stringEncoder = StringEncoder(self.fullEncoder.targetProgram)

    lazy val selfAndString = self.fullEncoder andThen stringEncoder
    lazy val bagEncoder = BagEncoder(selfAndString)(self.evaluator)

    lazy val setEncoder = SetEncoder(bagEncoder.targetProgram)

    lazy val bvEncoder = BitvectorEncoder(setEncoder.targetProgram)

    lazy val realEncoder = RealEncoder(bvEncoder.targetProgram)

    // @nv: Required due to limitations in scalac existential types
    protected lazy val e1 = stringEncoder andThen bagEncoder
    protected lazy val e2 = e1 andThen setEncoder
    protected lazy val e3 = e2 andThen bvEncoder
    lazy val theories = e3 andThen realEncoder
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

