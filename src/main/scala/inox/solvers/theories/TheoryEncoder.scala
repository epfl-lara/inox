/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._

trait TheoryEncoder extends ast.ProgramTransformer { self =>
  val targetProgram: Program { val trees: sourceProgram.trees.type }
  lazy val trees: sourceProgram.trees.type = sourceProgram.trees
}

trait SimpleEncoder extends TheoryEncoder with ast.ProgramEncoder {
  val t: sourceProgram.trees.type = sourceProgram.trees
}

object NoEncoder {
  def apply(p: Program): TheoryEncoder {
    val sourceProgram: p.type
    val targetProgram: Program { val trees: p.trees.type }
  } = new TheoryEncoder {
    val sourceProgram: p.type = p
    val targetProgram: Program { val trees: p.trees.type } =
      p.asInstanceOf[Program { val trees: p.trees.type }]

    import trees._
    protected object encoder extends IdentityTreeTransformer
    protected object decoder extends IdentityTreeTransformer
  }
}

