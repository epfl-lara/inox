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


    def fromInox(fd: trees.FunDef): Option[Function] =
      try {
        Some(Function(
          fd.id,
          Some(fd.id.name),
          fd.tparams.map(SimpleBindings.fromInox(_)),
          fd.params.map(SimpleBindings.fromInox(_).get),
          SimpleTypes.fromInox(fd.returnType).get,
          Eventual.pure(fd.returnType)))
      }
      catch {
        case _: Exception => None
      }
  }
}