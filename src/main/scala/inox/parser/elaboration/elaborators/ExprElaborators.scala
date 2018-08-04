package inox
package parser
package elaboration
package elaborators

trait ExprElaborators { self: Elaborators =>

  import Exprs._
  import SimpleTypes._

  implicit object ExprE extends Elaborator[Expr, Unknown, Eventual[trees.Expr]] {
    override def elaborate(template: Expr, expected: Unknown)(implicit store: Store): Constrained[Eventual[trees.Expr]] = ???
  }

  implicit object ExprSeqE extends HSeqE(ExprE)
}