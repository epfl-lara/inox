/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input._

trait TypeParsers { self: Parsers =>

  class TypeParser
    extends StdTokenParsers
       with PositionalErrors
       with StringContextParsers { self: ExpressionParser =>

    type Tokens = Lexer.type

    override val lexical = Lexer

    import TypeIR._
    import lexical.{Hole => _, _}

    def withPos(error: String, pos: Position) = ErrorLocation(error, pos).toString

    def p(c: Char): Parser[Token] = (elem(Parenthesis(c)) | elem(Punctuation(c))) withFailureMessage {
      (p: Position) => withPos("Expected character: " + c, p)
    }

    def kw(s: String): Parser[Token] = elem(Keyword(s)) withFailureMessage {
      (p: Position) => withPos("Expected keyword: " + s, p)
    }

    lazy val arrow = kw("=>") withFailureMessage {
      (p: Position) => withPos("Unexpected character. Arrow `=>` or end of type expected.", p)
    }

    lazy val typeExpression: Parser[Expression] = positioned(rep1sep(betweenArrows, arrow) flatMap {
      case tss => tss.reverse match {
        case returnTypes :: rest =>
          if (returnTypes.isEmpty) {
            failure("Illegal empty list of types.")
          } else if (returnTypes.lastOption.exists(_.isInstanceOf[TypeBinding])) {
            failure("Illegal type binding in last return type position.")
          } else {
            val retType = returnTypes match {
              case Seq(TypeSeqHole(i)) => Operation(Tuple, Seq(TypeSeqHole(i)))
              case Seq(t) => t
              case ts if ts.exists(_.isInstanceOf[TypeBinding]) => Operation(Sigma, ts)
              case ts => Operation(Tuple, ts)
            }

            success(rest.foldLeft(retType) {
              case (to, froms) => Operation(
                if (froms.exists(_.isInstanceOf[TypeBinding])) Pi else Arrow,
                Seq(Operation(Group, froms), to)
              )
            })
          }
        case Nil => throw new IllegalStateException("Empty list of types.")  // Should never happen.
      }
    }) withFailureMessage {
      (p: Position) => withPos("Type expected.", p)
    }

    lazy val betweenArrows: Parser[List[Expression]] = (
      ((p('(') ~ p(')')) ^^ (_ => Nil)) |
      argumentTypes('(', ')', allowNamed = true) |
      uniqueType) withFailureMessage {
      (p: Position) => withPos("Expected type or group of types.", p)
    }

    lazy val uniqueType: Parser[List[Expression]] = (typeHole | appliedType | parensType | refinementType) ^^ {
      case t => List(t)
    }

    def endOfGroup(c: Char) = p(c) withFailureMessage {
      (p: Position) => withPos("Expected character `" + c + "`, or more types (separated by `,`).", p)
    }

    def argumentTypes(open: Char, close: Char, allowNamed: Boolean = false): Parser[List[Expression]] = {
      val typeOrHole = if (allowNamed) typeSeqHole | typeBinding | typeExpression else typeSeqHole | typeExpression
      val typeOrEllipsis = ((typeOrHole ^^ (List(_))) | typeEllipsis) withFailureMessage {
        (p: Position) => withPos("Single type, or embedded sequence of types followed by `...`, expected.", p)
      }

      (p(open) ~> commit(rep1sep(typeOrEllipsis, p(',')) <~ endOfGroup(close))) ^^ (_.flatten) withFailureMessage {
        (p: Position) => withPos("Group of arguments expected.", p)
      }
    }

    lazy val parensType: Parser[Expression] = p('(') ~> typeExpression <~ p(')')

    lazy val name: Parser[Expression] = positioned(acceptMatch("Name", {
      case Embedded(t : trees.Type) => Literal(EmbeddedType(t))
      case Embedded(i : inox.Identifier) => Literal(EmbeddedIdentifier(i))
      case lexical.Identifier(s) => Literal(Name(s))
    }))

    lazy val typeSeqHole: Parser[Expression] = for {
      i <- acceptMatch("Hole", { case lexical.Hole(i) => i })
      _ <- kw("...")
    } yield (TypeSeqHole(i))

    lazy val typeHole: Parser[Expression] = for {
      i <- acceptMatch("Hole", { case lexical.Hole(i) => i })
      r <- opt(argumentTypes('[', ']'))
    } yield r match {
      case None => TypeHole(i)
      case Some(ts) => Application(NameHole(i), ts)
    }

    lazy val typeEllipsis: Parser[List[Expression]] = acceptMatch("Multiple embedded types", {
      case Embedded(ts: Traversable[_]) if ts.forall(_.isInstanceOf[trees.Type]) =>
        ts.map((t: Any) => Literal(EmbeddedType(t.asInstanceOf[trees.Type]))).toList
    }) <~ commit(kw("...") withFailureMessage {
      (p: Position) => withPos("Missing `...` after embedded sequence of types.", p)
    })

    lazy val appliedType: Parser[Expression] = for {
      n <- name
      oArgs <- opt(argumentTypes('[', ']'))
    } yield oArgs match {
      case None => n
      case Some(args) => Application(n, args)
    }

    lazy val refinementType: Parser[Expression] = for {
      _ <- p('{')
      (oid ~ tpe) <- commit(opt(identifier <~ p(':')) ~ typeExpression)
      _ <- commit(elem(Operator("|")))
      pred <- commit(expression)
      _ <- commit(p('}'))
    } yield Refinement(oid, tpe, pred)

    lazy val typeBinding: Parser[Expression] = for {
      id <- identifier
      _ <- p(':')
      tpe <- commit(typeExpression)
    } yield TypeBinding(id, tpe)
  }
}
