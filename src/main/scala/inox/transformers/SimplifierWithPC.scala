/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

import inox.solvers.{SimpleSolverAPI, SolverFactory}

/** Uses solvers to perform PC-aware simplifications */
trait SimplifierWithPC extends TransformerWithPC { self =>

  import program._
  import trees._
  import symbols._

  protected val sf: SolverFactory{ val program: self.program.type }
  protected lazy val s = SimpleSolverAPI(sf)

  private def querie(e: Expr, path: Path, implied: Boolean) = {
    val underTest = if (implied) e else Not(e)
    try {
      s.solveVALID(path implies underTest).contains(true)
    } catch {
      case _: Throwable =>
        false
    }
  }

  protected final def impliedBy(e: Expr, path: Path) = querie(e, path, true)
  protected final def contradictedBy(e: Expr, path: Path) = querie(e, path, false)

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

    case Assume(pred, body) if impliedBy(pred, path) =>
      rec(body, path)

    case Assume(pred, body) if contradictedBy(pred, path) =>
      Assume(BooleanLiteral(false), rec(body, path))

    case b if b.getType == BooleanType && impliedBy(b, path) =>
      BooleanLiteral(true).copiedFrom(b)

    case b if b.getType == BooleanType && contradictedBy(b, path) =>
      BooleanLiteral(false).copiedFrom(b)

    case _ =>
      super.rec(e, path)
  }
}
