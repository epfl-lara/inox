package inox
package parser
package irs

trait Bindings { self: IRs =>

  object Bindings {

    sealed abstract class Binding extends IR {
      override def getHoles: Seq[Hole] = this match {
        case BindingHole(index) => Seq(Hole(index, HoleTypes.ValDef))
        case ExplicitValDef(identifier, tpe) => identifier.getHoles ++ tpe.getHoles
        case InferredValDef(identifier) => identifier.getHoles
      }
    }

    case class InferredValDef(identifier: Identifiers.Identifier) extends Binding
    case class ExplicitValDef(identifier: Identifiers.Identifier, tpe: Types.Type) extends Binding
    case class BindingHole(index: Int) extends Binding

    type BindingSeq = HSeq[Binding]
  }

  implicit object holeTypableBinding extends HoleTypable[Bindings.Binding] {
    override val holeType = HoleTypes.ValDef
  }

}