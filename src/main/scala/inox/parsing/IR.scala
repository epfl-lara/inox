package inox
package parsing

import scala.util.parsing.input.Positional

/** Contains abstract Intermediate Representation (IR) language. */ 
trait IR {

  type Identifier  // Identifier of the language.
  type Type        // Types.
  type Operator    // Primitive operators.
  type Value       // Literal values.
  type Field       // Fields.
  type Quantifier  // Quantifiers.

  abstract class Expression(pre: String) extends Positional with Product {
    override def productPrefix = pos + "@" + pre
  }
  case class Variable(identifier: Identifier) extends Expression("Variable")
  case class Application(callee: Expression, args: Seq[Expression]) extends Expression("Application")
  case class Abstraction(quantifier: Quantifier, bindings: Seq[(Identifier, Option[Type])], body: Expression) extends Expression("Abstraction")
  case class Operation(operator: Operator, args: Seq[Expression]) extends Expression("Operation")
  case class Selection(structure: Expression, field: Field) extends Expression("Selection")
  case class Literal(value: Value) extends Expression("Literal")
  case class TypeApplication(callee: Expression, args: Seq[Type]) extends Expression("TypeApplication")
  case class Let(bindings: Seq[(Identifier, Option[Type], Expression)], body: Expression) extends Expression("Let")
}
