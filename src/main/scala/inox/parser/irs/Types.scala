package inox
package parser
package irs

trait Types { self: IRs =>

  object Types {
    sealed abstract class Type extends IR {
      override def getHoles: Seq[Hole] = this match {
        case FunctionType(froms, to) => froms.getHoles ++ to.getHoles
        case TupleType(elems) => elems.getHoles
        case Invocation(id, args) => id.getHoles ++ args.getHoles
        case Variable(id) => id.getHoles
        case RefinementType(binding, pred) => binding.getHoles ++ pred.getHoles
        case PiType(bindings, to) => bindings.getHoles ++ to.getHoles
        case SigmaType(bindings, to) => bindings.getHoles ++ to.getHoles
      }
    }

    case class FunctionType(froms: HSeq[Type], to: Type) extends Type
    case class TupleType(elems: HSeq[Type]) extends Type
    case class Invocation(identifier: Identifiers.Identifier, args: HSeq[Type]) extends Type
    case class Variable(identifier: Identifiers.Identifier) extends Type
    case class RefinementType(binding: Bindings.Binding, pred: Exprs.Expr) extends Type
    case class PiType(bindings: Bindings.BindingSeq, to: Type) extends Type
    case class SigmaType(bindings: Bindings.BindingSeq, to: Type) extends Type
  }
}