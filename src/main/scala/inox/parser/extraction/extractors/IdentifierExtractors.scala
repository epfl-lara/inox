package inox
package parser
package extraction
package extractors

trait IdentifierExtractors { self: Extractors =>

  import Identifiers._

  class ExprUseIdX extends Extractor[Identifier, inox.Identifier, Unit] {
    override def extract(template: Identifier, scrutinee: inox.Identifier): Matching[Unit] = template match {
      case IdentifierHole(index) => Matching(index -> scrutinee)
      case IdentifierName(name) => Matching.ensureConsistent(name, scrutinee, isType=false)
    }
  }
  val ExprUseIdX = new ExprUseIdX

  class TypeUseIdX extends Extractor[Identifier, inox.Identifier, Unit] {
    override def extract(template: Identifier, scrutinee: inox.Identifier): Matching[Unit] = template match {
      case IdentifierHole(index) => Matching(index -> scrutinee)
      case IdentifierName(name) => Matching.ensureConsistent(name, scrutinee, isType=true)
    }
  }
  val TypeUseIdX = new TypeUseIdX

  class DefIdX extends Extractor[Identifier, inox.Identifier, Option[(String, inox.Identifier)]] {
    override def extract(template: Identifier, scrutinee: inox.Identifier): Matching[Option[(String, inox.Identifier)]] = template match {
      case IdentifierHole(index) => Matching(index -> scrutinee).withValue(None)
      case IdentifierName(name) => Matching.pure(Some(name -> scrutinee))
    }
  }
  val DefIdX = new DefIdX

  class DefIdSeqX extends HSeqX[Identifier, inox.Identifier, Option[(String, inox.Identifier)]](DefIdX, None)
  val DefIdSeqX = new DefIdSeqX

  class FieldIdX extends Extractor[Identifier, inox.Identifier, Unit] {
    override def extract(template: Identifier, scrutinee: inox.Identifier): Matching[Unit] = template match {
      case IdentifierHole(index) => Matching(index -> scrutinee)
      case IdentifierName(name) => Matching.conditionally(scrutinee.name == name)
    }
  }
  val FieldIdX = new FieldIdX
}