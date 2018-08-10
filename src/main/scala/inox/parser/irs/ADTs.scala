package inox
package parser
package irs

trait ADTs { self: IRs =>

  object ADTs {
    case class Sort(
      identifier: Identifiers.Identifier,
      typeParams: Identifiers.IdentifierSeq,
      constructors: ConstructorSeq) extends IR {

      override def getHoles =
        identifier.getHoles ++
        typeParams.getHoles ++
        constructors.getHoles
    }

    case class Constructor(
      identifier: Identifiers.Identifier,
      params: Bindings.BindingSeq) extends IR {

      override def getHoles =
        identifier.getHoles ++
        params.getHoles
    }

    type ConstructorSeq = HSeq[Constructor]
  }

  implicit object holeTypableConstructor extends HoleTypable[ADTs.Constructor] {
    override val holeType = HoleTypes.Constructor
  }
}