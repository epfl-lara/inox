package inox
package parser
package elaboration

trait SimpleBindings { self: SimpleTypes with Trees =>

  object SimpleBindings {
    case class Binding(id: inox.Identifier, tpe: SimpleTypes.Type)

    def fromInox(vd: trees.ValDef): Binding = Binding(vd.id, SimpleTypes.fromInox(vd.tpe))
  }
}