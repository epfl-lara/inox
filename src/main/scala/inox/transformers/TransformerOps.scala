/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

class TransformerOp[In, Env, Out](val app: (In, Env) => Out, val sup: (In, Env) => Out) {
  def apply(in: In, env: Env): Out = app(in, env)
}

trait TransformerWithExprOp extends Transformer {
  private[this] val op = new TransformerOp[s.Expr, Env, t.Expr](transform(_, _), super.transform(_, _))

  val exprOp: (s.Expr, Env, TransformerOp[s.Expr, Env, t.Expr]) => t.Expr

  override def transform(e: s.Expr, env: Env): t.Expr = exprOp(e, env, op)
}
