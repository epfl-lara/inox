/* Copyright 2017 EPFL, Lausanne */

package inox
package parser

import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._

import inox.parser.sc.StringContextLexer

object Lexer extends StdLexical with StringContextLexer {

  reserved ++= Seq("true", "false", "if", "else", "forall", "lambda", "choose", "let", "in", "assume", "def", "type", "is", "as")

  val operators = (Operators.binaries.flatMap(_.ops) ++ Operators.unaries).distinct

  case class CharLit(char: Char) extends Token { def chars = char.toString }
  case class DecimalLit(whole: String, trailing: String, repeating: String) extends Token { def chars = whole + "." + trailing + "(" + repeating + ")" }
  case class Parenthesis(parenthesis: Char) extends Token { def chars = parenthesis.toString }
  case class Punctuation(punctuation: Char) extends Token { def chars = punctuation.toString }
  case class Operator(operator: String) extends Token { def chars = operator }
  case class Hole(pos: Int) extends Token { def chars = "$" + pos }
  case class Primitive(name: String) extends Token { def chars = name }

  override def token: Parser[Token] =
    char | number | priorityKeywords | operator  | keywords | punctuation | parens | super.token

  val priorityKeywords =
    acceptSeq("->") ^^^ Keyword("->")

  val keywords =
    acceptSeq("@") ^^^ Keyword("@") |
    acceptSeq("=>") ^^^ Keyword("=>") |
    acceptSeq("...") ^^^ Keyword("...") |
    acceptSeq("…") ^^^ Keyword("...") |
    ('.' <~ not(whitespaceChar)) ^^^ Keyword(".") |
    acceptSeq("true") <~ not(identChar | digit) ^^^ Keyword("true") |
    acceptSeq("false") <~ not(identChar | digit) ^^^ Keyword("false") |
    acceptSeq("if") <~ not(identChar | digit) ^^^ Keyword("if") |
    acceptSeq("else") <~ not(identChar | digit) ^^^ Keyword("else") |
    acceptSeq("let") <~ not(identChar | digit) ^^^ Keyword("let") |
    acceptSeq("in") <~ not(identChar | digit) ^^^ Keyword("in") |
    acceptSeq("assume") <~ not(identChar | digit) ^^^ Keyword("assume") |
    acceptSeq("=") ^^^ Keyword("=") |
    acceptSeq("def") ^^^ Keyword("def") |
    acceptSeq("type") ^^^ Keyword("type") |
    acceptSeq("is") ^^^ Keyword("is") |
    acceptSeq("as") ^^^ Keyword("as") |
    acceptSeq("choose") ^^^ Keyword("choose") |
    acceptSeq("lambda") ^^^ Keyword("lambda") |
    acceptSeq("forall") ^^^ Keyword("forall") |
    '∀' ^^^ Keyword("forall") |
    'λ' ^^^ Keyword("lambda")

  val comma: Parser[Token] = ',' ^^^ Punctuation(',')
  val dot: Parser[Token] = '.' ^^^ Punctuation('.')
  val colon: Parser[Token] = ':' ^^^ Punctuation(':')
  val punctuation: Parser[Token] = comma | dot | colon

  val number = opt('-') ~ rep1(digit) ~ opt('.' ~> afterDot) ^^ {
    case s ~ ds ~ None => NumericLit(s.map(x => "-").getOrElse("") + ds.mkString)
    case s ~ ds ~ Some((ts, rs)) => DecimalLit(s.map(x => "-").getOrElse("") + ds.mkString, ts, rs.getOrElse(""))
  }

  val afterDot: Parser[(String, Option[String])] = rep(digit) ~ opt('(' ~> rep1(digit) <~ ')') ^^ {
    case ds ~ os => (ds.mkString, os.map(_.mkString))
  }

  val char = '`' ~> commit(elem("Character", (x: Char) => true) <~ '`') ^^ {
    CharLit(_)
  }


  val operator: Parser[Token] =
    operators.sortBy(-_.length).map(acceptSeq(_)).reduce(_ | _) ^^ { (xs: List[Char]) =>
      Operator(xs.mkString)
    }

  val parens: Parser[Token] = accept("parenthesis", {
      case c @ ('[' | ']' | '(' | ')' | '{' | '}') => Parenthesis(c)
    })

  override def toHole(index: Int): Token = Hole(index)
}
