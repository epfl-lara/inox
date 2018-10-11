/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

class TraverserOp[In, Env](val app: (In, Env) => Unit, val sup: (In, Env) => Unit) {
  def apply(in: In, env: Env): Unit = app(in, env)
}

trait TraverserWithExprOp extends Traverser {
  private[this] val op = new TraverserOp[trees.Expr, Env](traverse(_, _), super.traverse(_, _))

  protected val exprOp: (trees.Expr, Env, TraverserOp[trees.Expr, Env]) => Unit

  override def traverse(e: trees.Expr, env: Env): Unit = exprOp(e, env, op)
}

trait TraverserWithTypeOp extends Traverser {
  private[this] val op = new TraverserOp[trees.Type, Env](traverse(_, _), super.traverse(_, _))

  protected val typeOp: (trees.Type, Env, TraverserOp[trees.Type, Env]) => Unit

  override def traverse(tpe: trees.Type, env: Env): Unit = typeOp(tpe, env, op)
}
