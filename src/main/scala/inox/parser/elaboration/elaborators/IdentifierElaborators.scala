package inox
package parser
package elaboration
package elaborators

trait IdentifierElaborators { self: Elaborators =>

  import Identifiers._

  implicit object IdE extends Elaborator[Identifier, Unit, inox.Identifier] {
    override def elaborate(template: Identifier, context: Unit)(implicit store: Store): Constrained[inox.Identifier] = ???
  }

  implicit object IdSeqE extends HSeqE(IdE)
}