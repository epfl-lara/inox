package inox
package parser
package irs

trait Exprs { self: IRs =>

  object Exprs {
    sealed abstract class Quantifier
    case object Forall extends Quantifier
    case object Lambda extends Quantifier

    object Unary {
      sealed abstract class Operator
      case object Minus extends Operator
      case object Not extends Operator
      case object BVNot extends Operator
      case object StringLength extends Operator
    }

    object Binary {
      sealed abstract class Operator
      case object Plus extends Operator
      case object Minus extends Operator
      case object Times extends Operator
      case object Division extends Operator
      case object Modulo extends Operator
      case object Remainder extends Operator
      case object Implies extends Operator
      case object Equals extends Operator
      case object LessEquals extends Operator
      case object LessThan extends Operator
      case object GreaterEquals extends Operator
      case object GreaterThan extends Operator
      case object BVAnd extends Operator
      case object BVOr extends Operator
      case object BVXor extends Operator
      case object BVShiftLeft extends Operator
      case object BVAShiftRight extends Operator
      case object BVLShiftRight extends Operator
      case object StringConcat extends Operator
    }

    object Ternary {
      sealed abstract class Operator
      case object SubString extends Operator
    }

    object NAry {
      sealed abstract class Operator
      case object And extends Operator
      case object Or extends Operator
    }

    object Primitive {
      sealed abstract class Function(val name: String, val typeArgs: Int, val args: Int)
      case object SetAdd extends Function("setAdd", 1, 2)
      case object ElementOfSet extends Function("elementOfSet", 1, 2)
      case object SetIntersection extends Function("setIntersection", 1, 2)
      case object SetUnion extends Function("setUnion", 1, 2)
      case object SetDifference extends Function("setDifference", 1, 2)
      case object Subset extends Function("subset", 1, 2)
      case object BagAdd extends Function("bagAdd", 1, 2)
      case object MultiplicityInBag extends Function("multiplicityInBag", 1, 2)
      case object BagIntersection extends Function("bagIntersection", 1, 2)
      case object BagUnion extends Function("bagUnion", 1, 2)
      case object BagDifference extends Function("bagDifference", 1, 2)
      case object MapApply extends Function("mapApply", 2, 2)
      case object MapUpdated extends Function("mapUpdated", 2, 3)
    }

    object Casts {
      sealed abstract class Mode
      case object Widen extends Mode
      case object Narrow extends Mode
    }

    sealed trait Expr extends IR {
      override def getHoles: Seq[Hole] = this match {
        case ExprHole(index) => Seq(Hole(index, HoleTypes.Expr))
        case SetConstruction(optType, elems) => optType.toSeq.flatMap(_.getHoles) ++ elems.getHoles
        case BagConstruction(optType, elems) => optType.toSeq.flatMap(_.getHoles) ++ elems.getHoles
        case MapConstruction(optTypes, elems, default) => optTypes.toSeq.flatMap(_.getHoles) ++ elems.getHoles ++ default.getHoles
        case Variable(id) => id.getHoles
        case UnaryOperation(_, expr) => expr.getHoles
        case BinaryOperation(_, lhs, rhs) => lhs.getHoles ++ rhs.getHoles
        case TernaryOperation(_, lhs, mid, rhs) => lhs.getHoles ++ mid.getHoles ++ rhs.getHoles
        case NaryOperation(_, args) => args.getHoles
        case Invocation(id, typeArgs, args) => id.getHoles ++ typeArgs.toSeq.flatMap(_.getHoles) ++ args.getHoles
        case PrimitiveInvocation(_, typeArgs, args) => typeArgs.toSeq.flatMap(_.getHoles) ++ args.getHoles
        case Application(callee, args) => callee.getHoles ++ args.getHoles
        case Abstraction(_, bindings, body) => bindings.getHoles ++ body.getHoles
        case Let(binding, value, body) => binding.getHoles ++ value.getHoles ++ body.getHoles
        case If(condition, thenn, elze) => condition.getHoles ++ thenn.getHoles ++ elze.getHoles
        case Selection(structure, id) => structure.getHoles ++ id.getHoles
        case Tuple(exprs) => exprs.getHoles
        case TupleSelection(tuple, _) => tuple.getHoles
        case TypeAnnotation(expr, tpe) => expr.getHoles ++ tpe.getHoles
        case Choose(binding, body) => binding.getHoles ++ body.getHoles
        case Assume(pred, body) => pred.getHoles ++ body.getHoles
        case IsConstructor(expr, id) => expr.getHoles ++ id.getHoles
        case Cast(_, expr, _) => expr.getHoles
        case _ => Seq()
      }
    }

    case class ExprHole(index: Int) extends Expr
    case class UnitLiteral() extends Expr
    case class BooleanLiteral(value: Boolean) extends Expr
    case class IntegerLiteral(value: BigInt) extends Expr
    case class FractionLiteral(numerator: BigInt, denominator: BigInt) extends Expr
    case class StringLiteral(value: String) extends Expr
    case class CharLiteral(value: Char) extends Expr
    case class SetConstruction(optType: Option[Types.Type], elems: ExprSeq) extends Expr
    case class BagConstruction(optType: Option[Types.Type], elems: ExprPairSeq) extends Expr
    case class MapConstruction(optTypes: Option[Types.TypeSeq], elems: ExprPairSeq, default: Expr) extends Expr
    case class Variable(id: Identifiers.Identifier) extends Expr
    case class UnaryOperation(operator: Unary.Operator, expr: Expr) extends Expr
    case class BinaryOperation(operator: Binary.Operator, lhs: Expr, rhs: Expr) extends Expr
    case class TernaryOperation(operator: Ternary.Operator, lhs: Expr, mid: Expr, rhs: Expr) extends Expr
    case class NaryOperation(operator: NAry.Operator, args: ExprSeq) extends Expr
    case class Invocation(id: Identifiers.Identifier, typeArgs: Option[Types.TypeSeq], args: ExprSeq) extends Expr
    case class PrimitiveInvocation(fun: Primitive.Function, typeArgs: Option[Types.TypeSeq], args: ExprSeq) extends Expr
    case class Application(callee: Expr, args: ExprSeq) extends Expr
    case class Abstraction(quantifier: Quantifier, bindings: Bindings.BindingSeq, body: Expr) extends Expr
    case class Let(binding: Bindings.Binding, value: Expr, body: Expr) extends Expr
    case class If(condition: Expr, thenn: Expr, elze: Expr) extends Expr
    case class Selection(structure: Expr, id: Identifiers.Identifier) extends Expr
    case class Tuple(exprs: ExprSeq) extends Expr
    case class TupleSelection(tuple: Expr, index: Int) extends Expr
    case class TypeAnnotation(expr: Expr, tpe: Types.Type) extends Expr
    case class Choose(binding: Bindings.Binding, body: Expr) extends Expr
    case class Assume(pred: Expr, body: Expr) extends Expr
    case class IsConstructor(expr: Expr, constructor: Identifiers.Identifier) extends Expr
    case class Cast(mode: Casts.Mode, expr: Expr, target: Int) extends Expr

    type ExprSeq = HSeq[Expr]

    sealed abstract class ExprPair extends IR {
      override def getHoles: Seq[Hole] = this match {
        case Pair(lhs, rhs) => lhs.getHoles ++ rhs.getHoles
        case PairHole(index) => Seq(Hole(index, HoleTypes.Pair(HoleTypes.Expr, HoleTypes.Expr)))
      }
    }

    case class Pair(lhs: Expr, rhs: Expr) extends ExprPair
    case class PairHole(index: Int) extends ExprPair

    type ExprPairSeq = HSeq[ExprPair]
  }

  implicit object holeTypableExpr extends HoleTypable[Exprs.Expr] {
    override val holeType = HoleTypes.Expr
  }

  implicit object holeTypableExprPair extends HoleTypable[Exprs.ExprPair] {
    override val holeType = HoleTypes.Pair(HoleTypes.Expr, HoleTypes.Expr)
  }
}