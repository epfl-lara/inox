/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input.Position

case class ParsingException(error: String) extends Exception(error)

abstract class ElaborationException(val errors: Seq[ErrorLocation]) extends Exception(errors.map(_.toString).mkString("\n\n"))
case class ExpressionElaborationException(es: Seq[ErrorLocation]) extends ElaborationException(es)
case class TypeElaborationException(es: Seq[ErrorLocation]) extends ElaborationException(es)
case class ConstraintException(error: String, position: Position) extends ElaborationException(Seq(ErrorLocation(error, position)))