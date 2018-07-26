/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input.Position

trait DefinitionParsers { self: Parsers =>

  class DefinitionParser extends ExpressionParser {

    import TypeIR.{Expression => Type}
    import ExprIR.{Identifier, Expression}
    import DefinitionIR._
    import lexical._

    lazy val pipe = elem(Operator("|")) withFailureMessage { (p: Position) =>
      withPos("Unexpected character. Separator `|` or end of constructor list expected.", p)
    }

    lazy val param: Parser[(Identifier, Type)] = (for {
      id <- identifier
      _ <- commit(p(':'))
      tp <- commit(typeExpression)
    } yield (id, tp)) withFailureMessage {
      (p: Position) => withPos("Parameter declaration expected.", p)
    }

    lazy val params: Parser[Seq[(Identifier, Type)]] =
      (p('(') ~> repsep(param, p(',')) <~ p(')')) withFailureMessage {
        (p: Position) => withPos("Parameter list expected.", p)
      }

    lazy val tparams: Parser[Seq[Identifier]] = (opt(for {
      _ <- p('[')
      ids <- commit(rep1sep(identifier, p(','))) withFailureMessage {
        (p: Position) => withPos("Type parameters expected.", p)
      }
      _ <- commit(p(']')) withFailureMessage {
        (p: Position) => withPos("Expected character `]`, or more type parameters (separated by `,`).", p)
      }
    } yield ids) ^^ (_.toSeq.flatten)) withFailureMessage {
      (p: Position) => withPos("Type parameter list expected (or no type parameters).", p)
    }

    lazy val constructor: Parser[(Identifier, Seq[(Identifier, Type)])] = (for {
      id <- commit(identifier) withFailureMessage { (p: Position) => withPos("Constructor name expected.", p) }
      ps <- commit(params)
    } yield (id, ps)) withFailureMessage {
      (p: Position) => withPos("Constructor declaration expected.", p)
    }

    lazy val datatype: Parser[TypeDef] = for {
      _ <- kw("type")
      id <- commit(identifier)
      tps <- commit(tparams)
      _ <- commit(kw("="))
      conss <- commit(rep1sep(constructor, pipe))
    } yield TypeDef(id, tps, conss)

    lazy val function: Parser[FunDef] = for {
      _ <- kw("def")
      id <- commit(identifier)
      tps <- commit(tparams)
      ps <- commit(params)
      _ <- commit(p(':'))
      tpe <- commit(typeExpression)
      _ <- commit(kw("="))
      body <- commit(expression)
    } yield FunDef(id, tps, ps, tpe, body)
  }
}
