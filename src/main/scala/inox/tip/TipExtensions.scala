/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import smtlib.printer._
import smtlib.parser.Terms._
import smtlib.parser.Commands._
import smtlib.lexer.{Tokens => LT, _}
import smtlib.extensions.tip.{Parser => SMTParser, Lexer => SMTLexer}

object Tokens {
  import LT.ReservedWord

  case object Assume extends ReservedWord
  case object DatatypeInvariant extends ReservedWord
}

object Terms {
  case class Assume(pred: Term, body: Term) extends TermExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(assume ")
      ctx.print(pred)
      ctx.print(" ")
      ctx.print(body)
      ctx.print(")")
    }
  }
}

object Commands {
  case class DatatypeInvariant(name: SSymbol, sort: Sort, pred: Term) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(datatype-invariant ")
      ctx.print(name)
      ctx.print(" ")
      ctx.print(sort)
      ctx.print(" ")
      ctx.print(pred)
      ctx.print(")\n")
    }
  }

  case class DatatypeInvariantPar(syms: Seq[SSymbol], name: SSymbol, sort: Sort, pred: Term) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(datatype-invariant (par ")
      ctx.printNary(syms, "(", " ", ") ")
      ctx.print(name)
      ctx.print(" ")
      ctx.print(sort)
      ctx.print(" ")
      ctx.print(pred)
      ctx.print("))\n")
    }
  }
}

class TipLexer(reader: java.io.Reader) extends SMTLexer(reader) {
  import LT.Token

  override protected def toReserved(s: String): Option[Token] = s match {
    case "assume" => Some(Token(Tokens.Assume))
    case "datatype-invariant" => Some(Token(Tokens.DatatypeInvariant))
    case _ => super.toReserved(s)
  }
}

class TipParser(lexer: TipLexer) extends SMTParser(lexer) {
  import Terms._
  import Commands._

  override protected def parseTermWithoutParens: Term = getPeekToken.kind match {
    case Tokens.Assume =>
      eat(Tokens.Assume)
      val pred = parseTerm
      val body = parseTerm
      Assume(pred, body)

    case _ => super.parseTermWithoutParens
  }

  override protected def parseCommandWithoutParens: Command = getPeekToken.kind match {
    case Tokens.DatatypeInvariant =>
      eat(Tokens.DatatypeInvariant)
      getPeekToken.kind match {
        case LT.OParen =>
          eat(LT.OParen)
          eat(LT.Par)
          val tps = parseMany(parseSymbol _)
          val name = parseSymbol
          val sort = parseSort
          val pred = parseTerm
          eat(LT.CParen)
          DatatypeInvariantPar(tps, name, sort, pred)

        case _ =>
          val name = parseSymbol
          val sort = parseSort
          val pred = parseTerm
          DatatypeInvariant(name, sort, pred)
      }

    case _ => super.parseCommandWithoutParens
  }
}
