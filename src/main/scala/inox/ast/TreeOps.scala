
package inox
package ast

trait TreeOps { self: Trees =>

  trait SelfTransformer extends transformers.Transformer {
    val s: self.type = self
    val t: self.type = self
  }

  trait SelfTreeTransformer extends transformers.TreeTransformer {
    val s: self.type = self
    val t: self.type = self
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
    val s: self.type = self
    val t: self.type = self

    override def transform(syms: s.Symbols): t.Symbols = syms
  }

  trait Traverser extends transformers.Traverser {
    val trees: self.type = self
  }

  trait TreeTraverser extends transformers.TreeTraverser with Traverser
}
