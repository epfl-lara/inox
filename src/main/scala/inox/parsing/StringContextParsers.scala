/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.combinator.syntactical.TokenParsers

trait StringContextParsers { self: TokenParsers { type Tokens <: StringContextLexer } =>
  
  def getFromSC[A](sc: StringContext, args: Seq[Any])(parser: Parser[A]): A = parser(lexical.getReader(sc, args)) match {
    case NoSuccess(msg, _) => throw ParsingException(msg)
    case Success(value, _) => value
  }
}