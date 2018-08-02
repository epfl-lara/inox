/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

trait ExprIRs { self: IRs =>

  /** IR for expressions. */
  object ExprIR extends IR {

    sealed abstract class Identifier extends Positional {
      def getName: String
      def getFullName: String

      override def toString = pos + "@" + getFullName
    }
    case class IdentifierName(name: String) extends Identifier {
      override def getName = name
      override def getFullName = name
    }
    case class IdentifierIdentifier(identifier: inox.Identifier) extends Identifier {
      override def getName = identifier.name
      override def getFullName = identifier.uniqueName
    }
    case class IdentifierHole(index: Int) extends Identifier {
      override def getName = "$" + index
      override def getFullName = "$" + index
    }

    type Operator = String

    sealed abstract class Field extends Positional
    case class FieldName(name: String) extends Field
    case class FieldIdentifier(identifier: inox.Identifier) extends Field
    case class FieldHole(index: Int) extends Field

    type Type = TypeIR.Expression

    sealed abstract class Value
    case class EmbeddedExpr(expr: trees.Expr) extends Value
    case class EmbeddedValue(value: Any) extends Value
    case class NumericLiteral(value: String) extends Value
    case class DecimalLiteral(whole: String, trailing: String, repeating: String) extends Value
    case class StringLiteral(string: String) extends Value
    case class BooleanLiteral(value: Boolean) extends Value
    case class CharLiteral(value: Char) extends Value
    case object UnitLiteral extends Value

    sealed abstract class Quantifier
    case object Lambda extends Quantifier
    case object Forall extends Quantifier
    case object Exists extends Quantifier
    case object Choose extends Quantifier

    type Binding = (Identifier, Option[Type])

    case class ExpressionHole(index: Int) extends Expression("ExpressionHole")
    case class ExpressionSeqHole(index: Int) extends Expression("ExpressionSeqHole")

    def getHoleTypes(identifier: Identifier): Map[Int, HoleType] = identifier match {
      case IdentifierHole(i) => Map(i -> IdentifierHoleType)
      case _ => Map()
    }

    def getHoleTypes(field: Field): Map[Int, HoleType] = field match {
      case FieldHole(i) => Map(i -> IdentifierHoleType)
      case _ => Map()
    }

    def getHoleTypes(binding: Binding): Map[Int, HoleType] = binding match {
      case (identifier, optType) => getHoleTypes(identifier) ++ optType.map(TypeIR.getHoleTypes(_)).getOrElse(Map())
    }

    def getHoleTypes(expr: Expression): Map[Int, HoleType] = expr match {
      case Variable(identifier) => getHoleTypes(identifier)
      case ExpressionHole(i) => Map(i -> ExpressionHoleType)
      case ExpressionSeqHole(i) => Map(i -> SeqHoleType(ExpressionHoleType))
      case Selection(expr, field) => getHoleTypes(expr) ++ getHoleTypes(field)
      case Operation(_, args) => args.map(getHoleTypes(_)).fold(Map[Int, HoleType]())(_ ++ _)
      case Application(callee, args) => args.map(getHoleTypes(_)).fold(getHoleTypes(callee))(_ ++ _)
      case Literal(_) => Map()
      case Abstraction(_, bindings, body) => bindings.map({
        case (identifier, optType) => getHoleTypes(identifier) ++ optType.map(TypeIR.getHoleTypes(_)).getOrElse(Map())
      }).fold(getHoleTypes(body))(_ ++ _)
      case TypeApplication(callee, args) => args.map(TypeIR.getHoleTypes(_)).fold(getHoleTypes(callee))(_ ++ _)
      case Let(bindings, body) => bindings.map({
        case ((identifier, optType), expr) => getHoleTypes(identifier) ++ optType.map(TypeIR.getHoleTypes(_)).getOrElse(Map()) ++ getHoleTypes(expr)
      }).fold(getHoleTypes(body))(_ ++ _)
    }
  }
}
