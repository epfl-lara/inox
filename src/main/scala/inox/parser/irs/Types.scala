package inox
package parser
package irs

trait Types { self: IRs =>

  object Types {
    abstract class Type extends IR {
      override def getHoles: Seq[Hole] = this match {
        case TypeHole(index) => Seq(Hole(index, HoleTypes.Type))
        case Primitive(_) => Seq()
        case FunctionType(froms, to) => froms.getHoles ++ to.getHoles
        case TupleType(elems) => elems.getHoles
        case Invocation(id, args) => id.getHoles ++ args.getHoles
        case Variable(id) => id.getHoles
        case Operation(_, args) => args.getHoles
        case RefinementType(binding, pred) => binding.getHoles ++ pred.getHoles
        case PiType(bindings, to) => bindings.getHoles ++ to.getHoles
        case SigmaType(bindings, to) => bindings.getHoles ++ to.getHoles
      }
    }

    object Operators {
      abstract class Operator
      case object Set extends Operator
      case object Map extends Operator
      case object Bag extends Operator
    }

    object Primitives {
      abstract class Type
      case class BVType(size: Int) extends Type
      case object IntegerType extends Type
      case object StringType extends Type
      case object CharType extends Type
      case object BooleanType extends Type
      case object UnitType extends Type
      case object RealType extends Type
    }

    case class TypeHole(index: Int) extends Type
    case class Primitive(primitive: Primitives.Type) extends Type
    case class Operation(operator: Operators.Operator, elems: TypeSeq) extends Type
    case class FunctionType(froms: TypeSeq, to: Type) extends Type
    case class TupleType(elems: TypeSeq) extends Type
    case class Invocation(identifier: Identifiers.Identifier, args: TypeSeq) extends Type
    case class Variable(identifier: Identifiers.Identifier) extends Type
    case class RefinementType(binding: Bindings.Binding, pred: Exprs.Expr) extends Type
    case class PiType(bindings: Bindings.BindingSeq, to: Type) extends Type
    case class SigmaType(bindings: Bindings.BindingSeq, to: Type) extends Type

    type TypeSeq = HSeq[Type]
  }

  implicit object holeTypableType extends HoleTypable[Types.Type] {
    override val holeType = HoleTypes.Type
  }
}