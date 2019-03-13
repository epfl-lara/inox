package inox
package parser
package sc

import scala.util.parsing.combinator.syntactical.TokenParsers

trait StringContextParsers { self: TokenParsers { type Tokens <: StringContextLexer } =>

  def parseSC[A](sc: StringContext)(parser: Parser[A]): Either[String, A] = {
    parser(lexical.getReader(sc)) match {
      case NoSuccess(msg, _) => Left(msg)
      case Success(value, _) => Right(value)
    }
  }
}
