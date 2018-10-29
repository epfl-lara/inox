/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers.z3

import solvers.{z3 => _, _}
import unrolling._

import z3.scala._

object NativeZ3Solver

trait NativeZ3Solver extends Z3Unrolling { self =>

  override val name = "nativez3"

  protected val underlying = NativeZ3Solver.synchronized(new {
    val program: targetProgram.type = targetProgram
    val context = self.context
  } with AbstractZ3Solver {
    lazy val semantics = targetSemantics
  })

  override def free(): Unit = NativeZ3Solver.synchronized(super.free())
}
