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

    sealed abstract class Constructor extends IR

    case class ConstructorValue(
      identifier: Identifiers.Identifier,
      params: Bindings.BindingSeq) extends Constructor {

      override def getHoles =
        identifier.getHoles ++
        params.getHoles
    }

    case class ConstructorHole(index: Int) extends Constructor {
      override def getHoles = Seq(Hole(index, HoleTypes.Constructor))
    }

    type ConstructorSeq = HSeq[Constructor]
  }

  implicit object holeTypableConstructor extends HoleTypable[ADTs.Constructor] {
    override val holeType = HoleTypes.Constructor
  }
}