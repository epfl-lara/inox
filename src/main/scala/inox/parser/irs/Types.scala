package inox
package parser
package irs

trait Types { self: IRs =>

  object Types {
    sealed abstract class Type extends IR {
      override def getHoles: Seq[Hole] = this match {
        case FunctionType(froms, to) => froms.getHoles ++ to.getHoles
        case MapType(from, to) => from.getHoles ++ to.getHoles
        case SetType(elem) => elem.getHoles
        case BagType(elem) => elem.getHoles
        case TupleType(elems) => elems.getHoles
        case ADTType(id, args) => id.getHoles ++ args.getHoles
        case TypeParameter(id) => id.getHoles
        case RefinementType(binding, pred) => binding.getHoles ++ pred.getHoles
        case PiType(bindings, to) => bindings.getHoles ++ to.getHoles
        case SigmaType(bindings, to) => bindings.getHoles ++ to.getHoles
        case _ => Seq()
      }
    }

    case class UnitType() extends Type
    case class BooleanType() extends Type
    case class BitVectorType(size: Int) extends Type
    case class IntegerType() extends Type
    case class StringType() extends Type
    case class CharType() extends Type
    case class RealType() extends Type
    case class FunctionType(froms: HSeq[Type], to: Type) extends Type
    case class MapType(from: Type, to: Type) extends Type
    case class SetType(elem: Type) extends Type
    case class BagType(elem: Type) extends Type
    case class TupleType(elems: HSeq[Type]) extends Type
    case class ADTType(identifier: Identifiers.Identifier, args: HSeq[Type]) extends Type
    case class TypeParameter(identifier: Identifiers.Identifier) extends Type
    case class RefinementType(binding: Bindings.Binding, pred: Exprs.Expr) extends Type
    case class PiType(bindings: Bindings.BindingSeq, to: Type) extends Type
    case class SigmaType(bindings: Bindings.BindingSeq, to: Type) extends Type
  }
}