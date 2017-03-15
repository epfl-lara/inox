/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.z3

import solvers.{z3 => _, _}
import unrolling._

import z3.scala._

trait NativeZ3Solver extends Z3Unrolling { self =>

  override val name = "nativez3"

  protected object underlying extends {
    val program: targetProgram.type = targetProgram
    val options = self.options
  } with AbstractZ3Solver {
    lazy val semantics = targetSemantics
  }
}
