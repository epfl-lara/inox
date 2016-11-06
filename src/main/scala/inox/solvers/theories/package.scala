/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

package object theories {

  trait Z3Theories { self: unrolling.AbstractUnrollingSolver =>
    object theories extends {
      val sourceProgram: self.encoder.targetProgram.type = self.encoder.targetProgram
    } with StringEncoder
  }

  trait CVC4Theories { self: unrolling.AbstractUnrollingSolver =>
    object theories extends {
      val sourceProgram: self.encoder.targetProgram.type = self.encoder.targetProgram
      val evaluator: evaluators.DeterministicEvaluator { val program: self.encoder.targetProgram.type } = new {
        val program: self.encoder.targetProgram.type = self.encoder.targetProgram
        val options = self.options
      } with evaluators.DeterministicEvaluator {
        import program.trees._
        import evaluators.EvaluationResults._

        def eval(e: Expr, model: Map[ValDef, Expr]): EvaluationResult = {
          self.evaluator.eval(self.encoder.decode(e), model.map {
            case (vd, value) => self.encoder.decode(vd) -> self.encoder.decode(value)
          }) match {
            case Successful(value) => Successful(self.encoder.encode(value))
            case RuntimeError(message) => RuntimeError(message)
            case EvaluatorError(message) => EvaluatorError(message)
          }
        }
      }
    } with BagEncoder
  }
}

