package inox
package parser
package elaboration

trait SimpleFunctions { self: SimpleTypes with SimpleBindings =>

  object SimpleFunctions {
    case class Function(
      id: inox.Identifier,
      optName: Option[String],
      typeArgs: Seq[SimpleBindings.TypeBinding],
      args: Seq[SimpleBindings.Binding])
  }
}