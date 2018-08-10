package inox
package parser
package irs

trait Identifiers { self: IRs =>

  object Identifiers {
    sealed trait Identifier extends IR {
      override def getHoles = this match {
        case IdentifierHole(index) => Seq(Hole(index, HoleTypes.Identifier))
        case _ => Seq()
      }
    }
    case class IdentifierName(name: String) extends Identifier
    case class IdentifierHole(index: Int) extends Identifier

    type IdentifierSeq = HSeq[Identifier]
  }

  implicit object holeTypableIdentifier extends HoleTypable[Identifiers.Identifier] {
    override val holeType = HoleTypes.Identifier
  }
}