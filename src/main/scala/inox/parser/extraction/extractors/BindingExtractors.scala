package inox
package parser
package extraction
package extractors

trait BindingExtractors { self: Extractors =>

  import Bindings._

  object BindingX extends Extractor[Binding, trees.ValDef, Option[(String, inox.Identifier)]] {
    override def extract(template: Binding, scrutinee: trees.ValDef): Matching[Option[(String, inox.Identifier)]] = template match {
      case BindingHole(index) =>
        Matching(index -> scrutinee).withValue(None)
      case InferredValDef(identifier) =>
        DefIdX.extract(identifier, scrutinee.id)
      case ExplicitValDef(identifier, tpe) =>
        DefIdX.extract(identifier, scrutinee.id) <<
        TypeX.extract(tpe, scrutinee.tpe)
    }
  }

  object BindingSeqX extends HSeqX[Binding, trees.ValDef, Option[(String, inox.Identifier)]](BindingX, None)
}