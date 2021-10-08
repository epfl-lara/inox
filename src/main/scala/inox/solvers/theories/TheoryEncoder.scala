/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

import inox.transformers.TreeTransformer
import utils._

trait TheoryEncoder extends transformers.ProgramTransformer { self =>
  val targetProgram: Program { val trees: sourceProgram.trees.type }
  val trees: sourceProgram.trees.type = sourceProgram.trees
}

abstract class SimpleEncoder private(override val sourceProgram: Program)
                                    (override val t: sourceProgram.trees.type)
                                    (override protected val encoder: transformers.TreeTransformer {
                                      val s: sourceProgram.trees.type
                                      val t: sourceProgram.trees.type
                                    },
                                    override protected val decoder: transformers.TreeTransformer {
                                      val s: sourceProgram.trees.type
                                      val t: sourceProgram.trees.type
                                    },
                                    extraFunctions: Seq[t.FunDef],
                                    extraSorts: Seq[t.ADTSort])
  extends transformers.ProgramEncoder(t, sourceProgram, encoder, decoder)(extraFunctions = extraFunctions, extraSorts = extraSorts)
     with TheoryEncoder {
  def this(sourceProgram: Program,
           encoder: transformers.TreeTransformer {
             val s: sourceProgram.trees.type
             val t: sourceProgram.trees.type
           },
           decoder: transformers.TreeTransformer {
             val s: sourceProgram.trees.type
             val t: sourceProgram.trees.type
           },
           extraFunctions: Seq[sourceProgram.trees.FunDef] = Seq.empty,
           extraSorts: Seq[sourceProgram.trees.ADTSort] = Seq.empty) =
    this(sourceProgram)(sourceProgram.trees)(encoder, decoder, extraFunctions, extraSorts)
}

class NoEncoder private(val p: Program)
                       (override val sourceProgram: p.type,
                        override val targetProgram: Program { val trees: p.trees.type },
                        override val encoder: p.trees.ConcreteIdentityTreeTransformer,
                        override val decoder: p.trees.ConcreteIdentityTreeTransformer)
  extends TheoryEncoder with transformers.ProgramTransformer {

  def this(p: Program) =
    this(p)(p, p.asInstanceOf[Program { val trees: p.trees.type }], new p.trees.ConcreteIdentityTreeTransformer, new p.trees.ConcreteIdentityTreeTransformer)
}
