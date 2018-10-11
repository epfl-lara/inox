/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

class TransformerOp[In, Env, Out](val app: (In, Env) => Out, val sup: (In, Env) => Out) {
  def apply(in: In, env: Env): Out = app(in, env)
}

trait TransformerWithExprOp extends Transformer {
  private[this] val op = new TransformerOp[s.Expr, Env, t.Expr](transform(_, _), super.transform(_, _))

  protected val exprOp: (s.Expr, Env, TransformerOp[s.Expr, Env, t.Expr]) => t.Expr

  override def transform(e: s.Expr, env: Env): t.Expr = exprOp(e, env, op)
}

trait TransformerWithTypeOp extends Transformer {
  private[this] val op = new TransformerOp[s.Type, Env, t.Type](transform(_, _), super.transform(_, _))

  protected val typeOp: (s.Type, Env, TransformerOp[s.Type, Env, t.Type]) => t.Type

  override def transform(tpe: s.Type, env: Env): t.Type = typeOp(tpe, env, op)
}
