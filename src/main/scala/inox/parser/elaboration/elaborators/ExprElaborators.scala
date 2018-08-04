package inox
package parser
package elaboration
package elaborators

trait ExprElaborators { self: Elaborators =>

  import Exprs._
  import SimpleTypes._

  object ExprE {
    def elaborate(template: Expr, expected: Unknown)(implicit store: Store): Constrained[Eventual[trees.Expr]] = ???
  }
}