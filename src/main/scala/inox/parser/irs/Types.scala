package inox
package parser
package irs

trait Types { self: IRs =>

  object Types {
    sealed abstract class Type extends IR {
      override def getHoles: Seq[Hole] = this match {
        case FunctionType(froms, to) => froms.flatMap(_.getHoles) ++ to.getHoles
        case MapType(from, to) => from.getHoles ++ to.getHoles
        case SetType(elem) => elem.getHoles
        case BagType(elem) => elem.getHoles
        case TupleType(elems) => elems.flatMap(_.getHoles)
        case ADTType(id, args) => id.getHoles ++ args.flatMap(_.getHoles)
        case TypeParameter(id) => id.getHoles
        case TypeBinding(id, tpe) => id.getHoles ++ tpe.getHoles
        case RefinementType(id, tpe, pred) => id.toSeq.flatMap(_.getHoles) ++ tpe.getHoles ++ pred.getHoles
        case HoleType(index) => Seq(Hole(index, HoleTypes.Type))
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
    case class FunctionType(froms: Seq[Type], to: Type) extends Type
    case class MapType(from: Type, to: Type) extends Type
    case class SetType(elem: Type) extends Type
    case class BagType(elem: Type) extends Type
    case class TupleType(elems: Seq[Type]) extends Type
    case class ADTType(identifier: Identifiers.Identifier, args: Seq[Type]) extends Type
    case class TypeParameter(identifier: Identifiers.Identifier) extends Type
    case class TypeBinding(identifier: Identifiers.Identifier, underlying: Type) extends Type
    case class RefinementType(identifier: Option[Identifiers.Identifier], underlying: Type, pred: Exprs.Expr) extends Type
    case class HoleType(index: Int) extends Type

    type TypeSeq = HSeq[Type]
  }
}