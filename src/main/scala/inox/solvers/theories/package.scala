/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

package object theories {

  trait Z3Theories { self: unrolling.AbstractUnrollingSolver =>
    val theories = StringEncoder(self.encoder.targetProgram)
  }

  trait CVC4Theories { self: unrolling.AbstractUnrollingSolver =>
    val theories = BagEncoder(self.encoder, self.options)(self.evaluator)
  }

  trait PrincessTheories { self: unrolling.AbstractUnrollingSolver =>
    val stringEncoder = StringEncoder(self.encoder.targetProgram)
    val bagEncoder = BagEncoder(self.encoder andThen stringEncoder, self.options)(self.evaluator)
    val theories = stringEncoder andThen bagEncoder
  }
}

