/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

/** Symbol table transformer base type */
trait SymbolTransformer { self =>
  val s: ast.Trees
  val t: ast.Trees

  def transform(syms: s.Symbols): t.Symbols

  def compose(that: SymbolTransformer { val t: self.s.type }): SymbolTransformer {
    val s: that.s.type
    val t: self.t.type
  } = {
    /** Enables equality checks between symbol transformer compositions */
    class SymbolTransformerComposition(protected val lhs: self.type,
                                       protected val rhs: that.type)
                                      (override val s: rhs.s.type,
                                       override val t: self.t.type)
      extends SymbolTransformer {

      override def transform(syms: s.Symbols): t.Symbols = lhs.transform(rhs.transform(syms))

      override def equals(that: Any): Boolean = that match {
        // NOTE: there is a spurious warning saying:
        // "the type test for SymbolTransformerComposition cannot be checked at runtime because it's a local class"
        // but the type test actually works as expected
        case c: SymbolTransformerComposition => rhs == c.rhs && lhs == c.lhs
        case _ => false
      }

      override def hashCode: Int = 31 * rhs.hashCode + lhs.hashCode
    }

    new SymbolTransformerComposition(self, that)(that.s, self.t)
  }

  def andThen(that: SymbolTransformer {
    val s: self.t.type
  }): SymbolTransformer {
    val s: self.s.type
    val t: that.t.type
  } = {
    // the scala compiler doesn't realize that this relation must hold here
    that `compose` this.asInstanceOf[SymbolTransformer {
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
  def apply(trans: DefinitionTransformer): SymbolTransformer {
    val s: trans.s.type
    val t: trans.t.type
  } = {
    class Impl(override val s: trans.s.type,
               override val t: trans.t.type)
      extends SimpleSymbolTransformer {
      protected def transformFunction(fd: s.FunDef): t.FunDef = trans.transform(fd)
      protected def transformSort(sort: s.ADTSort): t.ADTSort = trans.transform(sort)
    }
    new Impl(trans.s, trans.t)
  }
}
