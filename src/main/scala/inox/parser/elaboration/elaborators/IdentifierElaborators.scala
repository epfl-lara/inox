package inox
package parser
package elaboration
package elaborators

trait IdentifierElaborators { self: Elaborators =>

  import Identifiers._

  class DefIdE extends Elaborator[Identifier, (inox.Identifier, Option[String])] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[(inox.Identifier, Option[String])] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail(invalidHoleType("Identifier")(template.pos))
        case Some(id) => Constrained.pure((id, None))
      }
      case IdentifierName(name) => Constrained.pure((inox.FreshIdentifier(name), Some(name)))
    }
  }
  val DefIdE = new DefIdE

  class ExprUseIdE extends Elaborator[Identifier, inox.Identifier] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[inox.Identifier] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail(invalidHoleType("Identifier")(template.pos))
        case Some(id) => Constrained.pure(id)
      }
      case IdentifierName(name) => store.getExprIdentifier(name) match {
        case None => Constrained.fail(noExprInScope(name)(template.pos))
        case Some(id) => Constrained.pure(id)
      }
    }
  }
  val ExprUseIdE = new ExprUseIdE

  class ExprUseIDOverloadE extends Elaborator[Identifier, Seq[inox.Identifier]] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[Seq[inox.Identifier]] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail(invalidHoleType("Identifier")(template.pos))
        case Some(id) => Constrained.pure(Seq(id))
      }
      case IdentifierName(name) =>
        store.getExprIdentifier(name) match {
          case None => store.getFunctions(name) match {
            case None => Constrained.fail(noExprInScope(name)(template.pos))
            case Some(identSequence) => Constrained.pure(identSequence)
          }
          case Some(a) => Constrained.pure(Seq(a))
        }
    }
  }

  val ExprUseIDOverloadE = new ExprUseIDOverloadE

  class TypeUseIdE extends Elaborator[Identifier, inox.Identifier] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[inox.Identifier] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail(invalidHoleType("Identifier")(template.pos))
        case Some(id) => Constrained.pure(id)
      }
      case IdentifierName(name) => store.getTypeIdentifier(name) match {
        case None => Constrained.fail(noTypeInScope(name)(template.pos))
        case Some(id) => Constrained.pure(id)
      }
    }
  }
  val TypeUseIdE = new TypeUseIdE

  class FieldIdE extends Elaborator[Identifier, (String, Seq[(inox.Identifier, inox.Identifier)])] {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[(String, Seq[(inox.Identifier, inox.Identifier)])] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail(invalidHoleType("Identifier")(template.pos))
        case Some(id) => Constrained.pure((id.name, store.getSortByField(id).toSeq.map((_, id))))
      }
      case IdentifierName(name) => Constrained.pure((name, store.getFieldByName(name)))
    }
  }
  val FieldIdE = new FieldIdE

  class DefIdSeqE extends HSeqE[Identifier, inox.Identifier, (inox.Identifier, Option[String])]("Identifier") {
    override val elaborator = DefIdE

    override def wrap(id: inox.Identifier, where: IR)(implicit store: Store): Constrained[(inox.Identifier, Option[String])] =
      Constrained.pure((id, None))
  }
  val DefIdSeqE = new DefIdSeqE

  class TypeVarDefE extends Elaborator[Identifier, SimpleBindings.TypeBinding] {
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
  val TypeVarDefE = new TypeVarDefE

  class TypeVarDefSeqE extends HSeqE[Identifier, inox.Identifier, SimpleBindings.TypeBinding]("Identifier") {
    override val elaborator = TypeVarDefE

    override def wrap(id: inox.Identifier, where: IR)(implicit store: Store): Constrained[SimpleBindings.TypeBinding] =
      Constrained.pure(SimpleBindings.TypeBinding(
        id,
        SimpleTypes.TypeParameter(id),
        Eventual.pure(trees.TypeParameter(id, Seq())),
        None))
  }
  val TypeVarDefSeqE = new TypeVarDefSeqE
}