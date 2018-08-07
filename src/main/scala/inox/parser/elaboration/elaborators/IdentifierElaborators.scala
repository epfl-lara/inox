package inox
package parser
package elaboration
package elaborators

trait IdentifierElaborators { self: Elaborators =>

  import Identifiers._

  object DefIdE extends Elaborator[Identifier, inox.Identifier] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[inox.Identifier] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(id) => Constrained.pure(id)
      }
      case IdentifierName(name) => Constrained.pure(inox.FreshIdentifier(name))
    }
  }

  object UseIdE extends Elaborator[Identifier, inox.Identifier] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[inox.Identifier] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(id) => Constrained.pure(id)
      }
      case IdentifierName(name) => store.getIdentifier(name) match {
        case None => Constrained.fail("TODO: Other error")
        case Some(id) => Constrained.pure(id)
      }
    }
  }

  object FieldIdE extends Elaborator[Identifier, Seq[(inox.Identifier, inox.Identifier)]] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[Seq[(inox.Identifier, inox.Identifier)]] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(id) => Constrained.pure(store.getField(id).map((_, id)))
      }
      case IdentifierName(name) => Constrained.pure(store.getField(name))
    }
  }
}