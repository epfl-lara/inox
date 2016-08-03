/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

/** Uses solvers to perform PC-aware simplifications */
trait SimplifierWithPC extends TransformerWithPC {

  import trees._
  import symbols.Path

  implicit protected val s = symbols

  // FIXME: This needs to be changed when SolverAPI's are available
  protected def impliedBy(e: Expr, path: Path) : Boolean
  protected def contradictedBy(e: Expr, path: Path) : Boolean
  protected def valid(e: Expr) : Boolean
  protected def sat(e: Expr) : Boolean

  protected override def rec(e: Expr, path: Path) = e match {
    case IfExpr(cond, thenn, _) if impliedBy(cond, path) =>
      rec(thenn, path)

    case IfExpr(cond, _, elze ) if contradictedBy(cond, path) =>
      rec(elze, path)

    case And(e +: _) if contradictedBy(e, path) =>
      BooleanLiteral(false).copiedFrom(e)

    case And(e +: es) if impliedBy(e, path) =>
      val remaining = if (es.size > 1) And(es).copiedFrom(e) else es.head
      rec(remaining, path)

    case Or(e +: _) if impliedBy(e, path) =>
      BooleanLiteral(true).copiedFrom(e)

    case Or(e +: es) if contradictedBy(e, path) =>
      val remaining = if (es.size > 1) Or(es).copiedFrom(e) else es.head
      rec(remaining, path)

    case Implies(lhs, rhs) if impliedBy(lhs, path) =>
      rec(rhs, path)

    case Implies(lhs, rhs) if contradictedBy(lhs, path) =>
      BooleanLiteral(true).copiedFrom(e)

    case a @ Assume(pred, body) if impliedBy(pred, path) =>
      body

    /* @nv TODO. what are we supposed to do here!?
    case a @ Assume(pred, body) if contradictedBy(pred, path) =>
      Error(body.getType, s"Assertion failed: $msg").copiedFrom(a)
    */

    case b if b.getType == BooleanType && impliedBy(b, path) =>
      BooleanLiteral(true).copiedFrom(b)

    case b if b.getType == BooleanType && contradictedBy(b, path) =>
      BooleanLiteral(false).copiedFrom(b)

    case _ =>
      super.rec(e, path)
  }
}
