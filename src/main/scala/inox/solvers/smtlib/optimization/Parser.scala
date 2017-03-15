/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.smtlib.optimization

import smtlib._
import smtlib.lexer.{Tokens => LT}
import smtlib.parser.Terms._
import smtlib.parser.Commands._

object Tokens {
  import LT.ReservedWord

  case object Maximize extends ReservedWord
  case object Minimize extends ReservedWord
  case object AssertSoft extends ReservedWord
}

class Lexer(reader: java.io.Reader) extends lexer.Lexer(reader) {
  import LT.Token

  override protected def toReserved(s: String): Option[Token] = s match {
    case "maximize" => Some(Token(Tokens.Maximize))
    case "minimize" => Some(Token(Tokens.Minimize))
    case "assert-soft" => Some(Token(Tokens.AssertSoft))
    case _ => super.toReserved(s)
  }
}

class Parser(lexer: Lexer) extends parser.Parser(lexer) {
  import Commands._

  override protected def parseCommandWithoutParens: Command = getPeekToken.kind match {
    case Tokens.Maximize =>
      eat(Tokens.Maximize)
      Maximize(parseTerm)

    case Tokens.Minimize =>
      eat(Tokens.Minimize)
      Minimize(parseTerm)

    case Tokens.AssertSoft =>
      eat(Tokens.AssertSoft)
      val term = parseTerm

      val optWeight = getPeekToken match {
        case t @ LT.Keyword("weight") =>
          nextToken
          Some(parseNumeral)
        case _ => None
      }

      val optGroup = getPeekToken match {
        case t @ LT.Keyword("id") =>
          nextToken
          Some(parseSymbol)
        case _ => None
      }

      AssertSoft(term, optWeight.map(_.value.intValue), optGroup.map(_.name))

    case _ => super.parseCommandWithoutParens
  }
}
