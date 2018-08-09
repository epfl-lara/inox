package inox
package parser
package elaboration

trait SimpleBindings { self: SimpleTypes with Trees with Constraints =>

  object SimpleBindings {
    case class TypeBinding(id: Identifier, tpe: SimpleTypes.Type, evTpe: Eventual[trees.Type], name: Option[String])

    case class Binding(id: inox.Identifier, tpe: SimpleTypes.Type, evValDef: Eventual[trees.ValDef], name: Option[String]) {
      val evTpe = evValDef.map(_.tpe)
    }

    def fromInox(vd: trees.ValDef): Option[Binding] = SimpleTypes.fromInox(vd.tpe).map { st =>
      Binding(vd.id, st, Eventual.pure(vd), None)
    }
  }
}