/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input.Position

trait TypeIRs { self: IRs =>

  object TypeIR extends IR {

    type Identifier = Nothing
    type Type = Nothing
    type Field = Nothing
    type Quantifier = Nothing

    sealed abstract class Value
    case class Name(name: String) extends Value { override def toString = name }
    case class EmbeddedType(tpe: trees.Type) extends Value { override def toString = tpe.toString }
    case class EmbeddedIdentifier(id: inox.Identifier) extends Value { override def toString = id.toString }

    sealed abstract class Operator
    case object Group extends Operator
    case object Tuple extends Operator
    case object Sigma extends Operator
    case object Arrow extends Operator
    case object Pi    extends Operator

    case class TypeHole(index: Int) extends Expression("TypeHole")
    case class NameHole(index: Int) extends Expression("NameHole")
    case class TypeSeqHole(index: Int) extends Expression("TypeSeqHole")

    case class Refinement(id: Option[ExprIR.Identifier], tpe: Expression, pred: ExprIR.Expression) extends Expression("RefinementType")
    case class TypeBinding(id: ExprIR.Identifier, tpe: Expression) extends Expression("TypeBinding")

    def getHoleTypes(expr: Expression): Map[Int, HoleType] = expr match {
        case Application(callee, args) => args.map(getHoleTypes(_)).fold(getHoleTypes(callee))(_ ++ _)
        case Operation(_, args) => args.map(getHoleTypes(_)).fold(Map[Int, HoleType]())(_ ++ _)
        case Refinement(id, tpe, pred) => id.map(ExprIR.getHoleTypes(_)).getOrElse(Map()) ++ getHoleTypes(tpe) ++ ExprIR.getHoleTypes(pred)
        case TypeBinding(id, tpe) => ExprIR.getHoleTypes(id) ++ getHoleTypes(tpe)
        case TypeHole(i) => Map(i -> TypeHoleType)
        case NameHole(i) => Map(i -> IdentifierHoleType)
        case TypeSeqHole(i) => Map(i -> SeqHoleType(TypeHoleType))
        case Literal(_) => Map()
    }
  }
}
