
package inox
package ast

trait TreeOps { self: Trees =>

  trait SelfTransformer extends transformers.Transformer {
    // The only value that can be assigned to `s` and `t` is `self`, but that has to be
    // done in a concrete class explicitly overriding `s` and `t`.
    // Otherwise, we can run into initialization issue.
    val s: self.type
    val t: self.type
  }

  trait SelfTreeTransformer extends transformers.TreeTransformer {
    val s: self.type
    val t: self.type
  }

  trait IdentityTransformer extends SelfTransformer {
    override def transform(id: Identifier, tpe: s.Type, env: Env): (Identifier, t.Type) = (id, tpe)
    override def transform(vd: s.ValDef, env: Env): t.ValDef = vd
    override def transform(e: s.Expr, env: Env): t.Expr = e
    override def transform(tpe: s.Type, env: Env): t.Type = tpe
    override def transform(flag: s.Flag, env: Env): t.Flag = flag
  }

  trait IdentityTreeTransformer extends IdentityTransformer with transformers.TreeTransformer

  trait IdentitySymbolTransformer extends transformers.SymbolTransformer {
    val s: self.type
    val t: self.type

    override def transform(syms: s.Symbols): t.Symbols = syms
  }

  trait SelfTraverser extends transformers.Traverser {
    val trees: self.type
  }

  trait SelfTreeTraverser extends transformers.TreeTraverser {
    val trees: self.type
  }

  // Implementation of these traits as classes, as a conveniance when we want to create an anonymous transformer/traverser.

  // As noted in SelfTransformer, we must override `s` and `t` to ensure correct initialization of fields
  // in the parents that use `s` and `t`.
  class ConcreteSelfTransformer(override val s: self.type, override val t: self.type) extends SelfTransformer {
    def this() = this(self, self)
  }

  class ConcreteSelfTreeTransformer(override val s: self.type, override val t: self.type) extends SelfTreeTransformer {
    def this() = this(self, self)
  }

  class ConcreteIdentityTransformer(override val s: self.type, override val t: self.type) extends IdentityTransformer {
    def this() = this(self, self)
  }

  class ConcreteIdentityTreeTransformer(override val s: self.type, override val t: self.type) extends IdentityTreeTransformer {
    def this() = this(self, self)
  }

  class ConcreteIdentitySymbolTransformer(override val s: self.type, override val t: self.type) extends IdentitySymbolTransformer {
    def this() = this(self, self)
  }

  class ConcreteSelfTraverser(override val trees: self.type) extends SelfTraverser {
    def this() = this(self)
  }

  class ConcreteSelfTreeTraverser(override val trees: self.type) extends SelfTreeTraverser {
    def this() = this(self)
  }
}
