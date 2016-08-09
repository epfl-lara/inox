/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

package object theories {

  trait Z3Theories { self: unrolling.AbstractUnrollingSolver =>
    object theories extends {
      val sourceProgram: self.program.type = self.program
    } with StringEncoder
  }

  trait CVC4Theories { self: unrolling.AbstractUnrollingSolver =>
    object theories extends {
      val sourceProgram: self.program.type = self.program
    } with BagEncoder
  }
}

