/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import scala.language.implicitConversions

import inox.parser._

trait Trees
  extends Expressions
     with Constructors
     with Deconstructors
     with Types
     with Definitions
     with Printers
     with TreeOps
     with Paths { self =>

  class UnsupportedTree(t: Tree, msg: String)(implicit ctx: Context)
    extends Unsupported(s"${t.asString(PrinterOptions.fromContext(ctx))}@${t.getPos} $msg")

  abstract class Tree extends utils.Positioned with Serializable {
    def copiedFrom(o: Trees#Tree): this.type = setPos(o)

    // @EK: toString is considered harmful for non-internal things. Use asString(ctx) instead.

    def asString(implicit opts: PrinterOptions): String = prettyPrint(this, opts)

    override def toString = asString(PrinterOptions())
  }

  val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps

  val dsl: DSL { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with DSL

  val interpolator: MacrosInterpolators { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with MacrosInterpolators

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
