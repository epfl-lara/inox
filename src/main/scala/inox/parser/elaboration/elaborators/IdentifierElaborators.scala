package inox
package parser
package elaboration
package elaborators

trait IdentifierElaborators { self: Elaborators =>

  import Identifiers._

  implicit object IdE extends Elaborator[Identifier, Mode, inox.Identifier] {
    override def elaborate(template: Identifier, mode: Mode)(implicit store: Store): Constrained[inox.Identifier] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail("TODO: Error")
        case Some(id) => Constrained.pure(id)
      }
      case IdentifierName(name) => mode match {
        case Modes.Use => store.getIdentifier(name) match {
          case None => Constrained.fail("TODO: Other error")
          case Some(id) => Constrained.pure(id)
        }
        case Modes.Def => Constrained.pure(inox.FreshIdentifier(name))
      }
    }
  }

  implicit object IdSeqE extends HSeqE[Identifier, Mode, inox.Identifier, inox.Identifier] {
    override val elaborator = IdE
    override def wrap(i: inox.Identifier)(implicit store: Store): inox.Identifier = i
  }

  sealed trait Mode
  object Modes {
    case object Use extends Mode
    case object Def extends Mode
  }
}