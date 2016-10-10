/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package solvers
package theories

import utils._

trait TheoryEncoder extends ast.TreeBijection {
  val sourceProgram: Program
  lazy val trees: sourceProgram.trees.type = sourceProgram.trees

  lazy val s: trees.type = trees
  lazy val t: trees.type = trees

  lazy val targetProgram: Program { val trees: TheoryEncoder.this.trees.type } = {
    sourceProgram.transform(encoder).withFunctions(newFunctions).withADTs(newADTs)
  }

  import trees._

  protected val treeEncoder: SelfTransformer
  protected val treeDecoder: SelfTransformer

  lazy val encoder = new ast.SymbolTransformer {
    val transformer: treeEncoder.type = treeEncoder
  }

  lazy val decoder = new ast.SymbolTransformer {
    val transformer: treeEncoder.type = treeEncoder
  }

  val newFunctions: Seq[FunDef] = Seq.empty
  val newADTs: Seq[ADTDefinition] = Seq.empty

  def >>(that: TheoryEncoder { val sourceProgram: TheoryEncoder.this.targetProgram.type }): TheoryEncoder {
    val sourceProgram: TheoryEncoder.this.sourceProgram.type
  } = new TheoryEncoder {
    val sourceProgram: TheoryEncoder.this.sourceProgram.type = TheoryEncoder.this.sourceProgram

    protected val treeEncoder: SelfTransformer = TheoryEncoder.this.treeEncoder andThen that.treeEncoder
    protected val treeDecoder: SelfTransformer = that.treeDecoder andThen TheoryEncoder.this.treeDecoder
  }
}

trait NoEncoder extends TheoryEncoder {
  import trees._

  protected val treeEncoder: SelfTransformer = TreeIdentity
  protected val treeDecoder: SelfTransformer = TreeIdentity
}

