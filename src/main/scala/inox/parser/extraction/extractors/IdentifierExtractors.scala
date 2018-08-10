package inox
package parser
package extraction
package extractors

trait IdentifierExtractors { self: Extractors =>

  import Identifiers._

  object UseIdX extends Extractor[Identifier, inox.Identifier, Unit] {
    override def extract(template: Identifier, scrutinee: inox.Identifier): Matching[Unit] = template match {
      case IdentifierHole(index) => Matching(index -> scrutinee)
      case IdentifierName(name) => Matching.ensureConsistent(name, scrutinee)
    }
  }

  object DefIdX extends Extractor[Identifier, inox.Identifier, Option[(String, inox.Identifier)]] {
    override def extract(template: Identifier, scrutinee: inox.Identifier): Matching[Option[(String, inox.Identifier)]] = template match {
      case IdentifierHole(index) => Matching(index -> scrutinee).withValue(None)
      case IdentifierName(name) => Matching.pure(Some(name -> scrutinee))
    }
  }

  object DefIdSeqX extends HSeqX[Identifier, inox.Identifier, Option[(String, inox.Identifier)]](DefIdX, None)

  object FieldIdX extends Extractor[Identifier, inox.Identifier, Unit] {
    override def extract(template: Identifier, scrutinee: inox.Identifier): Matching[Unit] = template match {
      case IdentifierHole(index) => Matching(index -> scrutinee)
      case IdentifierName(name) => Matching.conditionally(scrutinee.name == name)
    }
  }
}