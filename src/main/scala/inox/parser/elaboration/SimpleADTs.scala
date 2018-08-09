package inox
package parser
package elaboration

trait SimpleADTs { self: SimpleBindings with SimpleTypes with Trees with Constraints =>

  object SimpleADTs {

    case class Sort(
      id: inox.Identifier,
      optName: Option[String],
      typeParams: Seq[SimpleBindings.TypeBinding],
      constructors: Seq[Constructor])

    def fromInox(s: trees.ADTSort): Option[Sort] =
      try {
        Some(Sort(
          s.id,
          Some(s.id.name),
          s.tparams.map(SimpleBindings.fromInox(_)),
          s.constructors.map(fromInox(_).get)))
      }
      catch {
        case _: Exception => None
      }


    case class Constructor(
      id: inox.Identifier,
      optName: Option[String],
      params: Seq[SimpleBindings.Binding],
      sort: inox.Identifier)

    def fromInox(c: trees.ADTConstructor): Option[Constructor] =
      try {
        Some(Constructor(
          c.id,
          Some(c.id.name),
          c.fields.map(SimpleBindings.fromInox(_).get),
          c.sort))
      }
      catch {
        case _: Exception => None
      }
  }
}