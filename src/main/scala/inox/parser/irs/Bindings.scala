package inox
package parser
package irs

trait Bindings { self: IRs =>

  object Bindings {
    sealed abstract class Binding extends IR {
      override def getHoles: Seq[Hole] = this match {
        case BindingHole(index) => Seq(Hole(index, HoleTypes.ValDef))
        case _ => Seq()
      }
    }
    case class ValDef(identifier: Identifiers.Identifier, tpe: Types.Type) extends Binding
    case class BindingHole(index: Int) extends Binding

    type BindingSeq = HSeq[Binding]
  }
}