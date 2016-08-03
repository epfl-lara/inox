/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

/** Uses solvers to perform PC-aware simplifications */
trait SimplifierWithPC extends TransformerWithPC {

  import trees._
  import symbols.{Path, matchExpr, matchExprCaseConditions}

  implicit protected val s = symbols

  // FIXME: This needs to be changed when SolverAPI's are available
  protected def impliedBy(e: Expr, path: Path) : Boolean
  protected def contradictedBy(e: Expr, path: Path) : Boolean
  protected def valid(e: Expr) : Boolean
  protected def sat(e: Expr) : Boolean

  protected override def rec(e: Expr, path: Path) = e match {
    case Require(pre, body) if impliedBy(pre, path) =>
      body

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

    case me @ MatchExpr(scrut, cases) =>
      val rs = rec(scrut, path)

      var stillPossible = true

      val conds = matchExprCaseConditions(me, path)

      val newCases = cases.zip(conds).flatMap { case (cs, cond) =>
        if (stillPossible && sat(cond.toClause)) {

          if (valid(cond.toClause)) {
            stillPossible = false
          }

          Seq((cs match {
            case SimpleCase(p, rhs) =>
              SimpleCase(p, rec(rhs, cond))
            case GuardedCase(p, g, rhs) =>
              val newGuard = rec(g, cond)
              if (valid(newGuard))
                SimpleCase(p, rec(rhs,cond))
              else
                GuardedCase(p, newGuard, rec(rhs, cond withCond newGuard))
          }).copiedFrom(cs))
        } else {
          Seq()
        }
      }

      newCases match {
        case List() =>
          Error(e.getType, "Unreachable code").copiedFrom(e)
        case _ =>
          matchExpr(rs, newCases).copiedFrom(e)
      }

    case a @ Assert(pred, _, body) if impliedBy(pred, path) =>
      body

    case a @ Assert(pred, msg, body) if contradictedBy(pred, path) =>
      Error(body.getType, s"Assertion failed: $msg").copiedFrom(a)

    case b if b.getType == BooleanType && impliedBy(b, path) =>
      BooleanLiteral(true).copiedFrom(b)

    case b if b.getType == BooleanType && contradictedBy(b, path) =>
      BooleanLiteral(false).copiedFrom(b)

    case _ =>
      super.rec(e, path)
  }
}
