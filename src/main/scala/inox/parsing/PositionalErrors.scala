/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.input._

trait PositionalErrors { self: Parsers =>
  
  implicit class PositionalErrorsDecorator[A](parser: Parser[A]) {
    
    def withErrorMessage(onError: Position => String): Parser[A] = new Parser[A] {
      override def apply(input: Input) = parser(input) match {
        case s @ Success(_, _) => s
        case e @ Error(_, rest) => Error(onError(input.pos), rest)
        case f @ Failure(_, _) => f
      }
    }

    def withFailureMessage(onFailure: Position => String): Parser[A] = new Parser[A] {
      override def apply(input: Input) = parser(input) match {
        case s @ Success(_, _) => s
        case e @ Error(_, _) => e
        case f @ Failure(_, rest) => Failure(onFailure(input.pos), rest)
      }
    }
  }
}