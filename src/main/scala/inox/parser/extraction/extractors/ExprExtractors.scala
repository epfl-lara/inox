package inox
package parser
package extraction
package extractors

trait ExprExtractors { self: Extractors =>
  import Exprs._
  implicit object ExprX extends Extractor[Expr, trees.Expr] {
    override def extract(template: Expr, scrutinee: trees.Expr): Matching = ???
  }

  implicit object ExprSeqX extends HSeqX(ExprX)
}