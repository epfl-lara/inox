package inox
package parser
package elaboration
package elaborators

trait TypeElaborators { self: Elaborators =>

  import Types._

  implicit object TypeE extends Elaborator[Type, Option[inox.Identifier], Eventual[trees.Type]] {
    override def elaborate(template: Type, context: Option[inox.Identifier])(implicit store: Store): Constrained[Eventual[trees.Type]] = ???
  }

  implicit object TypeSeqE extends HSeqE(TypeE)
}