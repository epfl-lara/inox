package inox
package parser
package extraction
package extractors

trait IdentifierExtractors { self: Extractors =>
  import Identifiers._
  implicit object IdX extends Extractor[Identifier, inox.Identifier, Option[(String, inox.Identifier)]] {
    override def extract(template: Identifier, scrutinee: inox.Identifier): Matching[Option[(String, inox.Identifier)]] = template match {
      case IdentifierHole(index) => Matching(index -> scrutinee).withValue(None)
      case IdentifierName(name) => Matching.ensureConsistent(name, scrutinee)
    }
  }
}