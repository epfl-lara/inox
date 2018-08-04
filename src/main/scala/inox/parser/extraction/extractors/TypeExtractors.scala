package inox
package parser
package extraction
package extractors

trait TypeExtractors { self: Extractors =>
  import Types._
  object TypeX extends Extractor[Type, trees.Type] {
    override def extract(template: Type, scrutinee: trees.Type): Matching = ???
  }
}