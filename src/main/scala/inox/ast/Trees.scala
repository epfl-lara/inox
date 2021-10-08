/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import scala.language.implicitConversions

import inox.parsing.Interpolator

trait Trees
  extends Expressions
     with Constructors
     with Deconstructors
     with Types
     with Definitions
     with Printers
     with TreeOps
     with Paths { self =>

  class UnsupportedTree(t: Tree, msg: String)(using ctx: Context)
    extends Unsupported(s"${t.asString(using PrinterOptions.fromContext(ctx))}@${t.getPos} $msg")

  abstract class Tree extends utils.Positioned with Serializable {
    def copiedFrom(o: Trees#Tree): this.type = setPos(o)

    // @EK: toString is considered harmful for non-internal things. Use asString(ctx) instead.

    def asString(using opts: PrinterOptions): String = prettyPrint(this, opts)

    override def toString = asString(using PrinterOptions())
  }

  val exprOps: ExprOps { val trees: self.type } = {
    class ExprOpsImpl(override val trees: self.type) extends ExprOps(trees)
    new ExprOpsImpl(this)
  }

  val dsl: DSL { val trees: self.type } = {
    class DSLImpl(override val trees: self.type) extends DSL
    new DSLImpl(this)
  }

  val interpolator: Interpolator { val trees: self.type } = {
    class InterpolatorImpl(override val trees: self.type) extends Interpolator with parsing.IRs
    new InterpolatorImpl(this)
  }

  def aliased(id1: Identifier, id2: Identifier) = {
    id1.toString == id2.toString
  }

  /** Returns true if the two group of identifiers ovelap. */
  def aliased(ids1: Set[Identifier], ids2: Set[Identifier]) = {
    val s1 = ids1.groupBy{ _.toString }.keySet
    val s2 = ids2.groupBy{ _.toString }.keySet
    (s1 & s2).nonEmpty
  }

  def aliasedSymbols[T1 <: VariableSymbol,T2 <: VariableSymbol](vs1: Set[T1], vs2: Set[T2]): Boolean = {
    aliased(vs1.map(_.id), vs2.map(_.id))
  }
}
