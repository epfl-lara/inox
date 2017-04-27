/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._

import inox.InoxProgram

trait Lexers { self: Interpolator =>

  object Lexer extends StdLexical with StringContextLexer {

    reserved ++= Seq("true", "false", "if", "else", "exists", "forall", "lambda", "choose", "let", "in", "assume")

    val unaryOps: Seq[String] = Operators.unaries
    val opTable: Seq[Level] = Operators.binaries 
    val operators = (opTable.flatMap(_.ops) ++ unaryOps).distinct

    case class CharLit(char: Char) extends Token { def chars = char.toString }
    case class Parenthesis(parenthesis: Char) extends Token { def chars = parenthesis.toString }
    case class Punctuation(punctuation: Char) extends Token { def chars = punctuation.toString }
    case class Quantifier(quantifier: String) extends Token { def chars = quantifier }
    case class Operator(operator: String) extends Token { def chars = operator }
    case class Embedded(value: Any) extends Token { def chars = value.toString }
    case class Hole(pos: Int) extends Token { def chars = "$" + pos }

    override def token: Parser[Token] =
      char | number | operator | keywords | punctuation | parens | quantifier | super.token

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
      acceptSeq("=") ^^^ Keyword("=")

    val comma: Parser[Token] = ',' ^^^ Punctuation(',')
    val dot: Parser[Token] = '.' ^^^ Punctuation('.')
    val colon: Parser[Token] = ':' ^^^ Punctuation(':')
    val punctuation: Parser[Token] = comma | dot | colon

    val number = rep1(digit) ~ opt('.' ~> rep1(digit)) ^^ {
      case ds ~ None     => NumericLit(ds.mkString)
      case ds ~ Some(rs) => NumericLit(ds.mkString + "." + rs.mkString)
    }

    val char = '`' ~> commit(elem("Character", (x: Char) => true) <~ '`') ^^ {
      CharLit(_)
    }

    val quantifier: Parser[Token] =
      '∀' ^^^ Quantifier("forall") |
      '∃' ^^^ Quantifier("exists") |
      'λ' ^^^ Quantifier("lambda") |
      acceptSeq("forall") ^^^ Quantifier("forall") |
      acceptSeq("exists") ^^^ Quantifier("exists") |
      acceptSeq("lambda") ^^^ Quantifier("lambda") |
      acceptSeq("choose") ^^^ Quantifier("choose")


    val operator: Parser[Token] =
      operators.sortBy(-_.length).map(acceptSeq(_)).reduce(_ | _) ^^ { (xs: List[Char]) =>
        Operator(xs.mkString)
      }

    val parens: Parser[Token] = accept("parenthesis", {
        case c@('[' | ']' | '(' | ')' | '{' | '}') => Parenthesis(c)
      })

    override def argToToken(x: Any): Token = x match {
      case MatchPosition(i) => Hole(i)
      case _ => Embedded(x)
    }
  }
}