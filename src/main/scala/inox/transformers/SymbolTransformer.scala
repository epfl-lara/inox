/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

/** Symbol table transformer base type */
trait SymbolTransformer { self =>
  val s: ast.Trees
  val t: ast.Trees

  def transform(syms: s.Symbols): t.Symbols

  /** Enables equality checks between symbol transformer compositions */
  protected trait SymbolTransformerComposition extends SymbolTransformer {
    protected val lhs: SymbolTransformer
    protected val rhs: SymbolTransformer { val t: lhs.s.type }

    val s: rhs.s.type = rhs.s
    val t: lhs.t.type = lhs.t

    override def transform(syms: s.Symbols): t.Symbols = lhs.transform(rhs.transform(syms))

    override def equals(that: Any): Boolean = that match {
      case c: SymbolTransformerComposition => rhs == c.rhs && lhs == c.lhs
      case _ => false
    }

    override def hashCode: Int = 31 * rhs.hashCode + lhs.hashCode
  }

  def compose(that: SymbolTransformer { val t: self.s.type }): SymbolTransformer {
    val s: that.s.type
    val t: self.t.type
  } = new {
    val rhs: that.type = that
    val lhs: self.type = self
  } with SymbolTransformerComposition

  def andThen(that: SymbolTransformer {
    val s: self.t.type
  }): SymbolTransformer {
    val s: self.s.type
    val t: that.t.type
  } = {
    // the scala compiler doesn't realize that this relation must hold here
    that compose this.asInstanceOf[SymbolTransformer {
      val s: self.s.type
      val t: that.s.type
    }]
  }
}

trait SimpleSymbolTransformer extends SymbolTransformer { self =>
  protected def transformFunction(fd: s.FunDef): t.FunDef
  protected def transformSort(sort: s.ADTSort): t.ADTSort

  def transform(syms: s.Symbols): t.Symbols = t.NoSymbols
    .withFunctions(syms.functions.values.toSeq.map(transformFunction))
    .withSorts(syms.sorts.values.toSeq.map(transformSort))
}

object SymbolTransformer {
  def apply(trans: Transformer): SymbolTransformer {
    val s: trans.s.type
    val t: trans.t.type
  } = new SimpleSymbolTransformer {
    val s: trans.s.type = trans.s
    val t: trans.t.type = trans.t

    protected def transformFunction(fd: s.FunDef): t.FunDef = trans.transform(fd)
    protected def transformSort(sort: s.ADTSort): t.ADTSort = trans.transform(sort)
  }
}
