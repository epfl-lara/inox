package inox
package parser
package extraction
package extractors

trait BindingExtractors { self: Extractors =>
  import Bindings._
  implicit object BindingX extends Extractor[Binding, trees.ValDef] {
    override def extract(template: Binding, scrutinee: trees.ValDef): Matching = template match {
      case BindingHole(index) =>
        Matching(index -> scrutinee)
      case InferredValDef(identifier) =>
        IdX.extract(identifier, scrutinee.id)
      case ExplicitValDef(identifier, tpe) =>
        IdX.extract(identifier, scrutinee.id) <>
        TypeX.extract(tpe, scrutinee.tpe)
      case UnnamedValDef(tpe) =>
        TypeX.extract(tpe, scrutinee.tpe)
    }
  }

  implicit object BindingSeqX extends HSeqX(BindingX)
}