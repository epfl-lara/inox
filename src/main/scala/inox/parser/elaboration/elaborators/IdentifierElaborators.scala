package inox
package parser
package elaboration
package elaborators

trait IdentifierElaborators { self: Elaborators =>

  import Identifiers._

  object IdE {
    def elaborate(template: Identifier)(implicit store: Store): Constrained[inox.Identifier] = ???
  }
}