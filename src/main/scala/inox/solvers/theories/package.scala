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
    } with BagEncoder
  }
}

