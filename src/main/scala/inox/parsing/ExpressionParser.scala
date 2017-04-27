/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input.Position

trait ExpressionParsers { self: Interpolator =>

  class ExpressionParser extends TypeParser {

    import lexical.{Identifier => _, Quantifier => _, Hole => _, _}
    
    import ExprIR._

    lazy val expression: Parser[Expression] = positioned(greedyRight | operatorExpr) withFailureMessage {
      (p: Position) => withPos("Expression expected.", p)
    }
    lazy val nonOperatorExpr: Parser[Expression] = positioned(withPrefix(greedyRight | withTypeAnnotation(selectionExpr))) withFailureMessage {
      (p: Position) => withPos("Expression expected.", p)
    }

    lazy val selectableExpr: Parser[Expression] = withApplication {
      invocationExpr | holeExpr | literalExpr | variableExpr | literalSetLikeExpr | tupleOrParensExpr
    }

    def withTypeAnnotation(exprParser: Parser[Expression]): Parser[Expression] = {
      for {
        e <- exprParser
        ot <- opt(p(':') ~> commit(typeExpression))
      } yield ot match {
        case None => e
        case Some(t) => TypeApplication(Operation("TypeAnnotation", Seq(e)), Seq(t))
      }
    }

    def withApplication(exprParser: Parser[Expression]): Parser[Expression] =
      for {
        expr <- exprParser
        argss <- rep(arguments) 
      } yield {
        argss.foldLeft(expr) {
          case (acc, args) => Application(acc, args)
        }
      }

    lazy val prefix: Parser[Expression => Expression] = unaryOps.map({
      (op: String) => elem(Operator(op)) ^^^ { (x: Expression) => Operation(op, Seq(x)) }
    }).reduce(_ | _)

    def withPrefix(exprParser: Parser[Expression]): Parser[Expression] =
      for {
        pres <- rep(prefix)
        expr <- exprParser
      } yield {
        pres.foldRight(expr) {
          case (pre, acc) => pre(acc)
        }
      }

    lazy val selectionExpr: Parser[Expression] = {
        
      val selector = (for {
        i <- positioned(selectorIdentifier)
        targs <- opt(typeArguments)
        argss <- rep(arguments) 
      } yield { (expr: Expression) =>
        val zero: Expression = if (targs.isDefined) {
          TypeApplication(Selection(expr, i).setPos(i.pos), targs.get).setPos(i.pos)
        } else {
          Selection(expr, i).setPos(i.pos)
        } 

        argss.foldLeft(zero) {
          case (acc, args) => Application(acc, args)
        }
      }) withFailureMessage {
        (p: Position) => withPos("Selector expected.", p)
      }

      positioned(selectableExpr) ~ rep(kw(".") ~> commit(selector)) ^^ {
        case expr ~ funs => funs.foldLeft(expr) {
          case (acc, f) => f(acc)
        }
      }
    }

    lazy val selectorIdentifier: Parser[Field] = acceptMatch("Selector", {
      case lexical.Identifier(name) => FieldName(name)
      case Embedded(i : inox.Identifier) => FieldIdentifier(i)
      case lexical.Hole(i) => FieldHole(i)
    })

    lazy val greedyRight: Parser[Expression] = quantifierExpr | ifExpr | letExpr | assumeExpr

    lazy val assumeExpr: Parser[Expression] = for {
      _ <- kw("assume")
      p <- commit(expression)
      _ <- commit(kw("in"))
      e <- commit(expression)
    } yield Operation("Assume", Seq(p, e))

    lazy val ifExpr: Parser[Expression] = for {
      _ <- kw("if")
      c <- commit(parensExpr withFailureMessage {
        (p: Position) => withPos("Missing condition, between parentheses '(' and ')'.", p)
      })
      t <- commit(expression)
      _ <- commit(kw("else") withFailureMessage {
        (p: Position) => withPos("Missing `else`. `if` expressions must have an accompanying `else`.", p)
      })
      e <- commit(expression)
    } yield Operation("IfThenElse", Seq(c, t, e))

    lazy val letExpr: Parser[Expression] = for {
      _  <- kw("let")
      bs <- commit(rep1sep(for {
          v <- valDef
          _ <- commit(kw("=") withFailureMessage {
              (p: Position) => withPos("Missing assignment to variable `" + v._1.getShortName +"`. Use `=` to assign a value to the variable.", p)
            })
          e <- commit(expression)
        } yield (v._1, v._2, e), p(',')) withFailureMessage {
          (p: Position) => withPos("Binding expected. Bindings take the form `variable = expression`, and are separated by `,`.", p)
        })
      _  <- commit(kw("in") withFailureMessage {
        (p: Position) => withPos("Missing `in`. `let` expressions must be followed by an expression introduced by the keyword `in`.", p)
      })
      bd <- commit(expression)
    } yield Let(bs, bd)

    lazy val holeExpr: Parser[Expression] = acceptMatch("Hole", {
      case lexical.Hole(i) => ExpressionHole(i)
    })

    lazy val holeExprSeq: Parser[Expression] = acceptMatch("Hole with ellipsis", {
      case lexical.Hole(i) => ExpressionSeqHole(i)
    }) <~ kw("...")


    lazy val literalExpr: Parser[Expression] = positioned(acceptMatch("Literal", {
      case Keyword("true")  => BooleanLiteral(true)
      case Keyword("false") => BooleanLiteral(false)
      case StringLit(s) => StringLiteral(s)
      case NumericLit(n) => NumericLiteral(n)
      case CharLit(c) => CharLiteral(c)
      case Embedded(e : trees.Expr) => EmbeddedExpr(e)
    }) ^^ (Literal(_)))

    lazy val variableExpr: Parser[Expression] = identifier ^^ (Variable(_))

    lazy val identifier: Parser[Identifier] = positioned(acceptMatch("Identifier", {
      case lexical.Identifier(name) => IdentifierName(name)
      case Embedded(i : inox.Identifier) => IdentifierIdentifier(i)
      case lexical.Hole(i) => IdentifierHole(i)
    })) withFailureMessage {
      (p: Position) => withPos("Identifier expected.", p)
    }

    lazy val parensExpr: Parser[Expression] = 
      (p('(') ~> commit(expression) <~ commit(p(')') withFailureMessage {
        (p: Position) => withPos("Missing `)`.", p)
      }))

    lazy val tupleOrParensExpr: Parser[Expression] =
      p('(') ~> repsep(expression, p(',')) <~ commit(p(')') withFailureMessage {
        (p: Position) => withPos("Missing `)`.", p)
      }) ^^ {
        case Seq() => Literal(UnitLiteral)
        case Seq(e) => e
        case es => Operation("Tuple", es)
      }

    def repsepOnce[A, B](parser: Parser[A], sep: Parser[Any], once: Parser[B]): Parser[(Option[B], Seq[A])] = {
      opt(rep1sepOnce(parser, sep, once)) ^^ {
        case None => (None, Seq())
        case Some(t) => t
      }
    }

    def rep1sepOnce[A, B](parser: Parser[A], sep: Parser[Any], once: Parser[B]): Parser[(Option[B], Seq[A])] =
      { 
        for {
          a <- parser
          o <- opt(sep ~> rep1sepOnce(parser, sep, once))
        } yield o match {
          case None => (None, Seq(a))
          case Some((ob, as)) => (ob, a +: as)
        }
      } | {
        for {
          b <- once
          o <- opt(sep ~> rep1sep(parser, sep))
        } yield o match {
          case None => (Some(b), Seq())
          case Some(as) => (Some(b), as)
        }
      }


    lazy val literalSetLikeExpr: Parser[Expression] =
      p('{') ~> repsepOnce(expression, p(','), defaultMap) <~ commit(p('}') withFailureMessage {
        (p: Position) => withPos("Missing `}`.", p)
      }) ^^ {
        case (None, as) => Operation("Set", as)
        case (Some((d, None)), as) => Operation("Map", d +: as)
        case (Some((d, Some(t))), as) => TypeApplication(Operation("Map", d +: as), Seq(t))
      }

    lazy val defaultMap: Parser[(Expression, Option[Type])] =
      for {
        _ <- elem(Operator("*"))
        ot <- opt(p(':') ~> typeExpression)
        _ <- commit(elem(Operator("->")) withFailureMessage {
          (p: Position) => withPos("Missing binding for the default case. Expected `->`.", p)
        })
        e <- expression
      } yield (e, ot)

    lazy val fdTable = symbols.functions.keys.toSet

    lazy val cstrTable = symbols.adts.toSeq.collect({
      case (i, cstr: trees.ADTConstructor) => i
    }).toSet

    lazy val symbolTable = fdTable ++ cstrTable

    lazy val symbol: Parser[Expression] = acceptMatch("Symbol", {
      case lexical.Identifier(name) if bi.names.contains(name) => Literal(Name(name))
      case lexical.Identifier(name) if symbolTable.map(_.name).contains(name) => Literal(Name(name))
      case Embedded(i : inox.Identifier) if symbolTable.contains(i) => Literal(EmbeddedIdentifier(i))
      case lexical.Hole(i) => ExpressionHole(i)
    })

    lazy val arguments: Parser[List[Expression]] = 
      p('(') ~> repsep(exprEllipsis | (holeExprSeq | expression) ^^ {List(_)}, p(',')) <~ commit(p(')') withFailureMessage {
        (p: Position) => withPos("Missing ')' at the end of the arguments.", p)
      }) ^^ {
        _.flatten
      }

    lazy val exprEllipsis: Parser[List[Expression]] = acceptMatch("Multiple embedded expressions", {
      case Embedded(es: Traversable[_]) if es.forall(_.isInstanceOf[trees.Expr]) =>
        es.map((e: Any) => Literal(EmbeddedExpr(e.asInstanceOf[trees.Expr]))).toList
    }) <~ commit(kw("...") withFailureMessage {
      (p: Position) => withPos("Missing `...` after embedded sequence of expressions.", p)
    })

    lazy val invocationExpr: Parser[Expression] = for {
      sb <- symbol
      otps <- opt(typeArguments)
      args <- arguments
    } yield otps match {
      case Some(tps) => Application(TypeApplication(sb, tps), args)
      case None => Application(sb, args)
    }

    lazy val quantifier: Parser[Quantifier] = acceptMatch("Quantifier expected.", {
      case lexical.Quantifier("forall") => Forall
      case lexical.Quantifier("exists") => Exists
      case lexical.Quantifier("lambda") => Lambda
      case lexical.Quantifier("choose") => Choose
    })

    lazy val valDef: Parser[(Identifier, Option[Type])] = for {
      i <- identifier
      otype <- opt(p(':') ~> commit(typeExpression))
    } yield (i, otype)

    def quantifierExpr: Parser[Expression] = for {
      q <- quantifier
      vds <- rep1sep(commit(valDef), p(','))
      _ <- commit(p('.') withFailureMessage {
        (p: Position) => "Missing `.` between bindings and expression body."
      })
      e <- commit(expression)
    } yield Abstraction(q, vds, e)

    lazy val operatorExpr: Parser[Expression] = {

      def operator(op: String) = (elem(Operator(op)) ^^^ { op }) withFailureMessage {
        (p: Position) => withPos("Unknown operator.", p)
      }

      def oneOf(ops: Seq[String]) = ops.map(operator(_)).reduce(_ | _) withFailureMessage {
        (p: Position) => withPos("Unknown operator.", p)
      }

      def toBinary(op: String): (Expression, Expression) => Expression =
        (a: Expression, b: Expression) => Operation(op, Seq(a, b))

      val zero = nonOperatorExpr

      Operators.binaries.foldLeft(zero) {
        case (morePrio, level) => {

          level match {
            case RightAssoc(ops) => {
              val bin = oneOf(ops).map(toBinary(_))
              morePrio ~ rep(bin ~ commit(morePrio)) ^^ {
                case first ~ opsAndExprs => {
                  if (opsAndExprs.isEmpty) {
                    first
                  }
                  else {
                    val (ops, exprs) = opsAndExprs.map({ case a ~ b => (a, b) }).unzip
                    val exprsAndOps = (first +: exprs).zip(ops)
                    val last = exprs.last

                    exprsAndOps.foldRight(last) {
                      case ((expr, f), acc) => f(expr, acc)
                    }
                  }
                }
              }
            }
            case LeftAssoc(ops) => {
              val bin = oneOf(ops).map(toBinary(_))
              chainl1(morePrio, bin)
            }
            case AnyAssoc(op) => {
              rep1sep(morePrio, operator(op)) ^^ {
                case Seq(x) => x
                case xs => Operation(op, xs)
              }
            }
          }
        }
      }
    }

    lazy val typeArguments: Parser[List[Type]] = p('[') ~> rep1sep(commit(typeExpression), p(',')) <~ commit(p(']') withFailureMessage {
      (p: Position) => withPos("Missing ']'.", p)
    })

    lazy val inoxValDef: Parser[trees.ValDef] = for {
      i <- identifier
      _ <- p(':')
      t <- inoxType
    } yield i match {
      case IdentifierIdentifier(v) => trees.ValDef(v, t)
      case IdentifierName(n) => trees.ValDef(FreshIdentifier(n), t)
      case IdentifierHole(_) => throw new scala.Error("Unexpected hole in value definition.")
    }
  }
}