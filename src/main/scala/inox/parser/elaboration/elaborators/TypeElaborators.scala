package inox
package parser
package elaboration
package elaborators

trait TypeElaborators { self: Elaborators =>

  import Types._

  object TypeE {
    def elaborate(template: Type, context: Option[inox.Identifier])(implicit store: Store): Constrained[Eventual[trees.Type]] = ???
  }
}