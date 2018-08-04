package inox
package parser
package extraction
package extractors

trait ExprExtractors { self: Extractors =>
  import Exprs._
  object ExprX extends Extractor[Expr, trees.Expr] {
    override def extract(template: Expr, scrutinee: trees.Expr): Matching = ???
  }
}