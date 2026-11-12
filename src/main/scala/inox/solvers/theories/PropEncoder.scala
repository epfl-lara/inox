/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package theories

import ast.QuantifierMode

/** Encodes propositions as booleans.
  *
  * A proposition has a truth value in every model, so solvers handle it as a boolean. The
  * encoded program types its quantifiers as booleans, and `PropType` is `BooleanType` in its
  * trees: predicate definitions return booleans, and the variables that name a proposition are
  * booleans.
  */
class PropEncoder private(override val sourceProgram: Program)
                         (override val t: sourceProgram.trees.type)
                         (encoder: sourceProgram.trees.ConcreteSelfTreeTransformer,
                          decoder: sourceProgram.trees.ConcreteIdentityTreeTransformer)
  extends transformers.ProgramEncoder(t, sourceProgram, encoder, decoder)(PropEncoder.erase(sourceProgram)(encoder))
     with TheoryEncoder {
  def this(sourceProgram: Program) = this(sourceProgram)(sourceProgram.trees)(
    PropEncoder.eraser(sourceProgram.trees), new sourceProgram.trees.ConcreteIdentityTreeTransformer)
}

object PropEncoder {
  def apply(p: Program): PropEncoder { val sourceProgram: p.type } = {
    class Impl(override val sourceProgram: p.type) extends PropEncoder(sourceProgram)
    new Impl(p)
  }

  private def eraser(trees: ast.Trees): trees.ConcreteSelfTreeTransformer = {
    import trees._
    new ConcreteSelfTreeTransformer {
      override def transform(tpe: Type): Type = tpe match {
        case PropType() => BooleanType()
        case _ => super.transform(tpe)
      }
    }
  }

  private def erase(p: Program)(eraser: p.trees.ConcreteSelfTreeTransformer): Program { val trees: p.trees.type } = {
    import p.trees._
    val hasProps = p.symbols.functions.values.exists { fd =>
      fd.returnType == PropType() || exprOps.exists {
        case Let(vd, _, _) => vd.tpe == PropType()
        case _ => false
      } (fd.fullBody)
    }
    if (!hasProps && p.symbols.modes.quantifiers == QuantifierMode.Boolean) {
      p.asInstanceOf[Program { val trees: p.trees.type }]
    } else {
      Program(p.trees)(p.symbols.transform(eraser).withQuantifiers(QuantifierMode.Boolean))
    }
  }
}
