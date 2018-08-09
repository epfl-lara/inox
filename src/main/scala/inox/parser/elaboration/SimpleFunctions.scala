package inox
package parser
package elaboration

trait SimpleFunctions { self: SimpleBindings with SimpleTypes with Trees with Constraints =>

  object SimpleFunctions {
    case class Function(
      id: inox.Identifier,
      optName: Option[String],
      typeParams: Seq[SimpleBindings.TypeBinding],
      params: Seq[SimpleBindings.Binding],
      retTpe: SimpleTypes.Type,
      evRetTpe: Eventual[trees.Type])
  }
}