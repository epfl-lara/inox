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
  } = SymbolTransformerComposition(self, that)

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
  
/** Enables equality checks between symbol transformer compositions */
class SymbolTransformerComposition(protected val left: SymbolTransformer, 
                                    protected val right: SymbolTransformer { val t: left.s.type })
                                    (override val s: right.s.type,
                                    override val t: left.t.type)
  extends SymbolTransformer {


  override def transform(syms: s.Symbols): t.Symbols = left.transform(right.transform(syms))

  override def equals(that: Any): Boolean = that match {
    // NOTE: there is a spurious warning saying:
    // "the type test for SymbolTransformerComposition cannot be checked at runtime because it's a local class"
    // but the type test actually works as expected
    case c: SymbolTransformerComposition => right == c.right && left == c.left
    case _ => false
  }

  override def hashCode: Int = 31 * right.hashCode + left.hashCode
}

object SymbolTransformerComposition {
  def apply(left: SymbolTransformer, right: SymbolTransformer {val t: left.s.type}): SymbolTransformer {
    val s: right.s.type
    val t: left.t.type
  } = 
    class LocalComposition(lhs: left.type, rhs: right.type, s: right.s.type, t: left.t.type) extends SymbolTransformerComposition(left, right)(s, t)
    new LocalComposition(left, right, right.s, left.t)
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
