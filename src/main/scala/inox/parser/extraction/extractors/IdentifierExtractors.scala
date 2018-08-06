package inox
package parser
package extraction
package extractors

trait IdentifierExtractors { self: Extractors =>
  import Identifiers._
  implicit object IdX extends Extractor[Identifier, inox.Identifier] {
    override def extract(template: Identifier, scrutinee: inox.Identifier): Matching = template match {
      case IdentifierHole(index) => Matching(index -> scrutinee)
      case IdentifierName(name) => Matching.ensureConsistent(name, scrutinee)
    }
  }

  implicit object IdSeqX extends HSeqX(IdX)
}