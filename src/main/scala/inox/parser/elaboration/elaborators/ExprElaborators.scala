package inox
package parser
package elaboration
package elaborators

trait ExprElaborators { self: Elaborators =>

  import Exprs._

  implicit object ExprE extends Elaborator[Expr, Unit, (SimpleTypes.Type, Eventual[trees.Expr])] {
    override def elaborate(template: Expr, context: Unit)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] = ???
  }

  implicit object ExprSeqE extends HSeqE[Expr, Unit, trees.Expr, (SimpleTypes.Type, Eventual[trees.Expr])] {
    override val elaborator = ExprE
    override def wrap(expr: trees.Expr)(implicit store: Store): (SimpleTypes.Type, Eventual[trees.Expr]) =
      (SimpleTypes.fromInox(expr.getType(store.getSymbols)), Eventual.pure(expr))
  }
}