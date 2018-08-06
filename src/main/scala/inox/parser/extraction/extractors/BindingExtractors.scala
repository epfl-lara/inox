package inox
package parser
package extraction
package extractors

trait BindingExtractors { self: Extractors =>
  import Bindings._
  implicit object BindingX extends Extractor[Binding, trees.ValDef, Option[(String, inox.Identifier)]] {
    override def extract(template: Binding, scrutinee: trees.ValDef): Matching[Option[(String, inox.Identifier)]] = template match {
      case BindingHole(index) =>
        Matching(index -> scrutinee).withValue(None)
      case InferredValDef(identifier) =>
        IdX.extract(identifier, scrutinee.id).shadowing
      case ExplicitValDef(identifier, tpe) =>
        IdX.extract(identifier, scrutinee.id).shadowing <<
        TypeX.extract(tpe, scrutinee.tpe)
    }
  }

  implicit object BindingSeqX extends HSeqX[Binding, trees.ValDef, Option[(String, inox.Identifier)]](BindingX, None)
}