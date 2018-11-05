package inox
package parser
package irs

trait Functions { self: IRs =>

  object Functions {
    case class Function(
      identifier: Identifiers.Identifier,
      typeParams: Identifiers.IdentifierSeq,
      params: Bindings.BindingSeq,
      returnType: Option[Types.Type],
      body: Exprs.Expr) extends IR {

      override def getHoles =
        identifier.getHoles ++
        typeParams.getHoles ++
        params.getHoles ++
        returnType.toSeq.flatMap(_.getHoles) ++
        body.getHoles
    }
  }
}