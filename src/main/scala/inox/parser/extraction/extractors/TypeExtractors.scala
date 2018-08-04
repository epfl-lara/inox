package inox
package parser
package extraction
package extractors

trait TypeExtractors { self: Extractors =>
  import Types._
  implicit object TypeX extends Extractor[Type, trees.Type] {
    override def extract(template: Type, scrutinee: trees.Type): Matching = ???
  }

  implicit object TypeSeqX extends HSeqX(TypeX)
}