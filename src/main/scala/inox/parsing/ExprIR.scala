package inox
package parsing

import scala.util.parsing.input._

trait ExprIRs extends ExpressionElaborators with ExpressionExtractors with ExpressionDeconstructors { self: Interpolator =>

  /** IR for expressions. */
  object ExprIR extends IR with ExpressionElaborator with ExpressionExtractor with ExpressionDeconstructor {

    sealed abstract class Identifier extends Positional {
      def getName: String
      def getShortName: String

      override def toString = pos + "@" + getName
    }
    case class IdentifierName(name: String) extends Identifier {
      override def getName = name
      override def getShortName = name
    }
    case class IdentifierIdentifier(identifier: inox.Identifier) extends Identifier {
      override def getName = identifier.uniqueName
      override def getShortName = identifier.toString
    }
    case class IdentifierHole(index: Int) extends Identifier {
      override def getName = "$" + index
      override def getShortName = "$" + index
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
    case class EmbeddedIdentifier(identifier: inox.Identifier) extends Value
    case class Name(name: String) extends Value
    case class NumericLiteral(value: String) extends Value
    case class StringLiteral(string: String) extends Value
    case class BooleanLiteral(value: Boolean) extends Value
    case class CharLiteral(value: Char) extends Value
    case object UnitLiteral extends Value

    sealed abstract class Quantifier
    case object Lambda extends Quantifier
    case object Forall extends Quantifier
    case object Exists extends Quantifier
    case object Choose extends Quantifier

    case class ExpressionHole(index: Int) extends Expression("ExpressionHole")
    case class ExpressionSeqHole(index: Int) extends Expression("ExpressionSeqHole")
  }
}