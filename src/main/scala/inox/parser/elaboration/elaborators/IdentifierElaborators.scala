package inox
package parser
package elaboration
package elaborators

trait IdentifierElaborators { self: Elaborators =>

  import Identifiers._

  object DefIdE extends Elaborator[Identifier, (inox.Identifier, Option[String])] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[(inox.Identifier, Option[String])] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(id) => Constrained.pure((id, None))
      }
      case IdentifierName(name) => Constrained.pure((inox.FreshIdentifier(name), Some(name)))
    }
  }

  object ExprUseIdE extends Elaborator[Identifier, inox.Identifier] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[inox.Identifier] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(id) => Constrained.pure(id)
      }
      case IdentifierName(name) => store.getExprIdentifier(name) match {
        case None => Constrained.fail("TODO: Other error")
        case Some(id) => Constrained.pure(id)
      }
    }
  }

  object TypeUseIdE extends Elaborator[Identifier, inox.Identifier] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[inox.Identifier] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(id) => Constrained.pure(id)
      }
      case IdentifierName(name) => store.getTypeIdentifier(name) match {
        case None => Constrained.fail("TODO: Other error")
        case Some(id) => Constrained.pure(id)
      }
    }
  }

  object FieldIdE extends Elaborator[Identifier, Seq[(inox.Identifier, inox.Identifier)]] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[Seq[(inox.Identifier, inox.Identifier)]] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(id) => Constrained.pure(store.getSortByField(id).toSeq.map((_, id)))
      }
      case IdentifierName(name) => Constrained.pure(store.getFieldByName(name))
    }
  }

  object DefIdSeqE extends HSeqE[Identifier, inox.Identifier, (inox.Identifier, Option[String])] {
    override val elaborator = DefIdE

    override def wrap(id: inox.Identifier)(implicit store: Store): Constrained[(inox.Identifier, Option[String])] =
      Constrained.pure((id, None))
  }

  object TypeVarDefE extends Elaborator[Identifier, SimpleBindings.TypeBinding] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[SimpleBindings.TypeBinding] = {
      DefIdE.elaborate(template).map { case (id, optName) =>
        SimpleBindings.TypeBinding(
          id,
          SimpleTypes.TypeParameter(id),
          Eventual.pure(trees.TypeParameter(id, Seq())),
          optName)
      }
    }
  }

  object TypeVarDefSeqE extends HSeqE[Identifier, inox.Identifier, SimpleBindings.TypeBinding] {
    override val elaborator = TypeVarDefE

    override def wrap(id: inox.Identifier)(implicit store: Store): Constrained[SimpleBindings.TypeBinding] =
      Constrained.pure(SimpleBindings.TypeBinding(
        id,
        SimpleTypes.TypeParameter(id),
        Eventual.pure(trees.TypeParameter(id, Seq())),
        None))
  }
}