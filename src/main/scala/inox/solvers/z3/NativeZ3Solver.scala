/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers.z3

import solvers.{z3 => _, _}
import unrolling._

import z3.scala._

object NativeZ3Solver

class NativeZ3Solver(prog: Program,
                     context: Context,
                     enc: transformers.ProgramTransformer {val sourceProgram: prog.type},
                     chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type})
                    (using semantics: prog.Semantics,
                     semanticsProvider: SemanticsProvider {val trees: enc.targetProgram.trees.type})
  extends Z3Unrolling(prog, context, enc, chooses) { self =>

  override val name = "nativez3"

  protected val underlying =
    NativeZ3Solver.synchronized(new Underlying(targetProgram, self.context)(using targetSemantics))

  override def free(): Unit = NativeZ3Solver.synchronized(super.free())

  private class Underlying(override val program: targetProgram.type,
                           override val context: Context)
                          (using override val semantics: targetSemantics.type)
    extends AbstractZ3Solver
}