package inox
package parser

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.input._

import inox.parser.sc.StringContextParsers

trait Parsers extends StringContextParsers with StdTokenParsers with PackratParsers with NumberUtils { self: IRs =>

  type Tokens = Lexer.type
  override val lexical = Lexer

  import Identifiers._
  import Bindings._
  import Exprs.{Primitive => PrimitiveFunctions, _}
  import Types.{Invocation => TypeInvocation, Operators => TypeOperators, _}
  import Functions._
  import ADTs._

  def p(c: Char): Parser[lexical.Token] =
    elem(lexical.Parenthesis(c)) | elem(lexical.Punctuation(c))

  def kw(s: String): Parser[lexical.Token] = elem(lexical.Keyword(s))

  def operator(s: String): Parser[lexical.Token] = elem(lexical.Operator(s))

  def hseqParser[A <: IR](rep: Parser[A], sep: Parser[Any], allowEmpty: Boolean=false)(implicit ev: HoleTypable[A]): Parser[HSeq[A]] = {
    val holeSeq: Parser[Either[Int, A]] = acceptMatch("hole", {
      case lexical.Hole(index) => Left(index)
    }) <~ elem(lexical.Keyword("..."))

    val nonEmpty = rep1sep(holeSeq | rep.map(Right(_)), sep).map(new HSeq[A](_))
    if (allowEmpty) {
      opt(nonEmpty).map(_.getOrElse(HSeq[A]()))
    }
    else {
      nonEmpty
    }
  }

  lazy val identifierParser: Parser[Identifier] = acceptMatch("identifier", {
    case lexical.Identifier(name) => IdentifierName(name)
    case lexical.Hole(index) => IdentifierHole(index)
  })

  lazy val holeParser: Parser[Int] = acceptMatch("hole", {
    case lexical.Hole(index) => index
  })

  lazy val typeParser: Parser[Type] = contextTypeParser(None)

  def contextTypeParser(context: Option[String]): Parser[Type] = {

    import Primitives.{Type => _, _}
    import TypeOperators._

    val typeHoleParser: Parser[Type] =
      holeParser ^^ { (index: Int) => TypeHole(index) }

    object PrimitiveType {
      def unapply(arg: String): Option[Primitives.Type] = arg match {
        case "Int" => Some(BVType(32))
        case "Integer" => Some(IntegerType)
        case "Real" => Some(RealType)
        case "Boolean" => Some(BooleanType)
        case "String" => Some(StringType)
        case "Char" => Some(CharType)
        case "Unit" => Some(UnitType)
        case _ if arg.startsWith("Int") => scala.util.Try {
          val size = BigInt(arg.drop(3))
          BVType(size.toInt)
        }.toOption
        case _ => None
      }
    }

    val primitiveParser = acceptMatch("type primitive", {
      case lexical.Identifier(PrimitiveType(tpe)) => Primitive(tpe)
    })

    object TypeOperator {
      def unapply(arg: String): Option[Operator] = arg match {
        case "Map" => Some(Map)
        case "Set" => Some(Set)
        case "Bag" => Some(Bag)
        case _ => None
      }
    }

    val typeOperatorParser: Parser[Operator] = acceptMatch("type operator", {
      case lexical.Identifier(TypeOperator(op)) => op
    })

    val operationParser: Parser[Type] =
      typeOperatorParser ~ (p('[') ~> hseqParser(typeParser, p(',')) <~ p(']')) ^^ {
        case op ~ args => Operation(op, args)
      }

    val invocationParser: Parser[Type] =
      identifierParser ~ (p('[') ~> hseqParser(typeParser, p(',')) <~ p(']')) ^^ {
        case id ~ args => TypeInvocation(id, args)
      }

    val inParensParser: Parser[Type] =
      p('(') ~> hseqParser(typeParser, p(',')) <~ p(')') ^^ {
        xs => if (xs.elems.size == 1 && xs.elems.head.isRight) xs.elems.head.right.get else TupleType(xs)
      }

    val sigmaTypeParser: Parser[Type] =
      p('(') ~> hseqParser(bindingParser(explicitOnly=true), p(',')) ~ (kw("->") ~> typeParser) <~ p(')') ^^ {
        case bs ~ tpe => SigmaType(bs, tpe)
      }

    val variableParser: Parser[Type] = identifierParser ^^ {
      case i => Types.Variable(i)
    }

    lazy val defaultNamedBinding: Parser[Binding] = context match {
      case None => failure("no default names available")
      case Some(name) => ret.map(tpe => ExplicitValDef(IdentifierName(name), tpe))
    }

    lazy val refinementTypeParser: Parser[Type] =
      p('{') ~> (bindingParser(explicitOnly=true) | defaultNamedBinding) ~ (operator("|") ~> exprParser) <~ p('}') ^^ {
        case binding ~ expr => RefinementType(binding, expr)
      }

    lazy val singleTypeParser: Parser[Type] =
      typeHoleParser       |
      primitiveParser      |
      operationParser      |
      invocationParser     |
      variableParser       |
      refinementTypeParser |
      inParensParser       |
      sigmaTypeParser

    lazy val typesGroup: Parser[HSeq[Type]] =
      (p('(') ~> hseqParser(typeParser, p(','), allowEmpty=true) <~ p(')')) |
      singleTypeParser ^^ { tpe => new HSeq[Type](Seq(Right(tpe))) }

    lazy val depTypesGroup: Parser[HSeq[Binding]] =
      (p('(') ~> hseqParser(bindingParser(explicitOnly=true), p(','), allowEmpty=true) <~ p(')'))

    lazy val ret = rep((typesGroup.map(Right(_)) <~ kw("=>")) | (depTypesGroup.map(Left(_)) <~ (kw("->") | kw("=>")))) ~ singleTypeParser ^^ { case as ~ b =>
      as.foldRight(b) {
        case (Left(xs), acc) => PiType(xs, acc)
        case (Right(xs), acc) => FunctionType(xs, acc)
      }
    }

    ret
  }

  lazy val exprParser: Parser[Expr] = {

    val exprHoleParser: Parser[Expr] =
      holeParser ^^ { i => ExprHole(i) }

    val ifParser: Parser[Expr] = for {
      _ <- kw("if")
      _ <- p('(')
      c <- exprParser
      _ <- p(')')
      t <- exprParser
      _ <- kw("else")
      e <- exprParser
    } yield If(c, t, e)

    val literalParser: Parser[Expr] = acceptMatch("literal expression", {
      case lexical.DecimalLit(whole, trailing, repeating) => {
        val (n, d) = toFraction(whole, trailing, repeating)
        FractionLiteral(n, d)
      }
      case lexical.NumericLit(number) =>
        IntegerLiteral(BigInt(number))
      case lexical.StringLit(string) =>
        StringLiteral(string)
      case lexical.CharLit(character) =>
        CharLiteral(character)
      case lexical.Keyword("true") =>
        BooleanLiteral(true)
      case lexical.Keyword("false") =>
        BooleanLiteral(false)
    })

    val unitLiteralParser: Parser[Expr] = p('(') ~> p(')') ^^^ UnitLiteral()

    val tupleParser: Parser[Expr] = p('(') ~> hseqParser(exprParser, p(',')) <~ p(')') ^^ { xs =>
      if (xs.elems.size == 1 && xs.elems.head.isRight) xs.elems.head.right.get else Tuple(xs)
    }

    val letParser: Parser[Expr] = for {
      _ <- kw("let")
      b <- bindingParser(explicitOnly=false)
      _ <- kw("=")
      v <- exprParser
      _ <- kw("in")
      e <- exprParser
    } yield Let(b, v, e)

    val lambdaParser: Parser[Expr] = for {
      _  <- kw("lambda")
      ps <- hseqParser(bindingParser(explicitOnly=false), p(','), allowEmpty=true)
      _  <- p('.')
      e  <- exprParser
    } yield Abstraction(Lambda, ps, e)

    val forallParser: Parser[Expr] = for {
      _  <- kw("forall")
      ps <- hseqParser(bindingParser(explicitOnly=false), p(','))
      _  <- p('.')
      e  <- exprParser
    } yield Abstraction(Forall, ps, e)

    val chooseParser: Parser[Expr] = for {
      _ <- kw("choose")
      b <- bindingParser(explicitOnly=false)
      _ <- p('.')
      e <- exprParser
    } yield Choose(b, e)


    val primitiveFunctions = Map(
      "elementOfSet" -> PrimitiveFunctions.ElementOfSet,
      "setAdd" -> PrimitiveFunctions.SetAdd,
      "setUnion" -> PrimitiveFunctions.SetUnion,
      "setIntersection" -> PrimitiveFunctions.SetIntersection,
      "setDifference" -> PrimitiveFunctions.SetDifference,
      "subset" -> PrimitiveFunctions.Subset,
      "bagAdd" -> PrimitiveFunctions.BagAdd,
      "multiplicity" -> PrimitiveFunctions.MultiplicityInBag,
      "bagIntersection" -> PrimitiveFunctions.BagIntersection,
      "bagUnion" -> PrimitiveFunctions.BagUnion,
      "bagDifference" -> PrimitiveFunctions.BagDifference,
      "apply" -> PrimitiveFunctions.MapApply,
      "updated" -> PrimitiveFunctions.MapUpdated)

    val primitiveNameParser: Parser[PrimitiveFunctions.Function] = acceptMatch("primitive function name", {
      case lexical.Identifier(name) if primitiveFunctions.contains(name) => primitiveFunctions(name)
    })

    val primitiveInvocationParser: Parser[Expr] = for {
      f   <- primitiveNameParser
      tps <- opt(p('[') ~> hseqParser(typeParser, p(',')) <~ p(']'))
      ps  <- p('(') ~> hseqParser(exprParser, p(','), allowEmpty=true) <~ p(')')
    } yield PrimitiveInvocation(f, tps, ps)

    val invocationParser: Parser[Expr] = for {
      i   <- identifierParser
      tps <- opt(p('[') ~> hseqParser(typeParser, p(',')) <~ p(']'))
      ps  <- p('(') ~> hseqParser(exprParser, p(','), allowEmpty=true) <~ p(')')
    } yield Invocation(i, tps, ps)

    val variableParser: Parser[Expr] = identifierParser ^^ {
      i => Exprs.Variable(i)
    }

    val nonOperatorParser: Parser[Expr] =
      exprHoleParser            |
      literalParser             |
      unitLiteralParser         |
      primitiveInvocationParser |
      invocationParser          |
      variableParser            |
      tupleParser               |
      ifParser                  |
      letParser                 |
      lambdaParser              |
      forallParser              |
      chooseParser

    val postfixedParser: Parser[Expr] = {

      object TupleSelector {
        def unapply(s: String): Option[Int] =
          if (s.startsWith("_")) scala.util.Try {
            BigInt(s.drop(1)).toInt
          }.toOption
          else None
      }

      val tupleSelectorParser: Parser[Int] = acceptMatch("tuple selector", {
        case lexical.Identifier(TupleSelector(i)) => i
      })

      val fieldParser = kw(".") ~> (tupleSelectorParser.map(Left(_)) | identifierParser.map(Right(_)))

      val argsParser = p('(') ~> hseqParser(exprParser, p(','), allowEmpty=true) <~p(')')

      val asParser = kw("as") ~> typeParser

      val isParser = kw("is") ~> identifierParser

      val postfixParser =
        fieldParser.map(i => Left(Left(i)))   |
        argsParser.map(as => Left(Right(as))) |
        asParser.map(tpe => Right(Left(tpe))) |
        isParser.map(i => Right(Right(i)))

      nonOperatorParser ~ rep(postfixParser) ^^ {
        case e ~ fs => fs.foldLeft(e) {
          case (acc, Left(Left(Left(i))))  => TupleSelection(acc, i - 1)
          case (acc, Left(Left(Right(i)))) => Selection(acc, i)
          case (acc, Left(Right(xs)))      => Application(acc, xs)
          case (acc, Right(Left(tpe)))     => TypeAnnotation(acc, tpe)
          case (acc, Right(Right(i)))      => IsConstructor(acc, i)
        }
      }
    }

    val operatorParser: Parser[Expr] = {

      val unaryParser: Parser[Expr] = {
        opt(Operators.unaries.map(operator(_)).reduce(_ | _)) ~ postfixedParser ^^ {
          case None ~ e => e
          case Some(lexical.Operator(o)) ~ e => o match {
            case "+" => e
            case "-" => UnaryOperation(Unary.Minus, e)
            case "~" => UnaryOperation(Unary.BVNot, e)
            case "!" => UnaryOperation(Unary.Not, e)
            case _ => throw new IllegalArgumentException("Unknown operator: " + o)
          }
        }
      }

      Operators.binaries.foldLeft(unaryParser) {
        case (acc, LeftAssoc(ops)) => acc ~ rep(ops.map(operator(_) ~ acc).reduce(_ | _)) ^^ {
          case first ~ pairs => {
            pairs.foldLeft(first) {
              case (acc, lexical.Operator("+") ~ elem) =>
                BinaryOperation(Binary.Plus, acc, elem)
              case (acc, lexical.Operator("-") ~ elem) =>
                BinaryOperation(Binary.Minus, acc, elem)
              case (acc, lexical.Operator("*") ~ elem) =>
                BinaryOperation(Binary.Times, acc, elem)
              case (acc, lexical.Operator("/") ~ elem) =>
                BinaryOperation(Binary.Division, acc, elem)
              case (acc, lexical.Operator("mod") ~ elem) =>
                BinaryOperation(Binary.Modulo, acc, elem)
              case (acc, lexical.Operator("%") ~ elem) =>
                BinaryOperation(Binary.Remainder, acc, elem)
              case (acc, lexical.Operator("==") ~ elem) =>
                BinaryOperation(Binary.Equals, acc, elem)
              case (acc, lexical.Operator("!=") ~ elem) =>
                UnaryOperation(Unary.Not, BinaryOperation(Binary.Equals, acc, elem))
              case (acc, lexical.Operator("<=") ~ elem) =>
                BinaryOperation(Binary.LessEquals, acc, elem)
              case (acc, lexical.Operator("<") ~ elem) =>
                BinaryOperation(Binary.LessThan, acc, elem)
              case (acc, lexical.Operator(">=") ~ elem) =>
                BinaryOperation(Binary.GreaterEquals, acc, elem)
              case (acc, lexical.Operator(">") ~ elem) =>
                BinaryOperation(Binary.GreaterThan, acc, elem)
              case (acc, lexical.Operator("&") ~ elem) =>
                BinaryOperation(Binary.BVAnd, acc, elem)
              case (acc, lexical.Operator("|") ~ elem) =>
                BinaryOperation(Binary.BVOr, acc, elem)
              case (acc, lexical.Operator("^") ~ elem) =>
                BinaryOperation(Binary.BVXor, acc, elem)
              case (acc, lexical.Operator("<<") ~ elem) =>
                BinaryOperation(Binary.BVShiftLeft, acc, elem)
              case (acc, lexical.Operator(">>") ~ elem) =>
                BinaryOperation(Binary.BVAShiftRight, acc, elem)
              case (acc, lexical.Operator(">>>") ~ elem) =>
                BinaryOperation(Binary.BVLShiftRight, acc, elem)
              case (acc, lexical.Operator("++") ~ elem) =>
                BinaryOperation(Binary.StringConcat, acc, elem)
              case (acc, lexical.Operator("∪") ~ elem) =>
                PrimitiveInvocation(PrimitiveFunctions.SetUnion, None, HSeq.fromSeq(Seq(acc, elem)))
              case (acc, lexical.Operator("∩") ~ elem) =>
                PrimitiveInvocation(PrimitiveFunctions.SetIntersection, None, HSeq.fromSeq(Seq(acc, elem)))
              case (acc, lexical.Operator("\\") ~ elem) =>
                PrimitiveInvocation(PrimitiveFunctions.SetDifference, None, HSeq.fromSeq(Seq(acc, elem)))
              case (acc, lexical.Operator("⊆") ~ elem) =>
                PrimitiveInvocation(PrimitiveFunctions.Subset, None, HSeq.fromSeq(Seq(acc, elem)))
              case (acc, lexical.Operator("∈") ~ elem) =>
                PrimitiveInvocation(PrimitiveFunctions.ElementOfSet, None, HSeq.fromSeq(Seq(acc, elem)))
              case (_, op ~ _) => throw new IllegalArgumentException("Unknown operator: " + op)
            }
          }
        }
        case (acc, RightAssoc(ops)) => acc ~ rep(ops.map(operator(_) ~ acc).reduce(_ | _)) ^^ {
          case first ~ pairs => {
            val os = pairs.map(_._1)
            val es = first +: pairs.map(_._2)
            (es.init.zip(os)).foldRight(es.last) {
              case ((elem, lexical.Operator("==>")), acc) => BinaryOperation(Binary.Implies, elem, acc)
              case ((_, op), _) => throw new IllegalArgumentException("Unknown operator: " + op)
            }
          }
        }
        case (acc, AnyAssoc(op)) => rep1sep(acc, operator(op)) ^^ { xs =>
          val nary = op match {
            case "&&" => NAry.And
            case "||" => NAry.Or
            case _ => throw new IllegalArgumentException("Unknown operator: " + op)
          }
          if (xs.length == 1) {
            xs.head
          }
          else {
            NaryOperation(nary, HSeq.fromSeq(xs))
          }
        }
      }
    }

    operatorParser
  }

  lazy val functionDefinitionParser: Parser[Function] = for {
    _  <- kw("def")
    i  <- identifierParser
    ts <- opt(p('[') ~> hseqParser(identifierParser, p(',')) <~ p(']'))
    ps <- p('(') ~> hseqParser(bindingParser(explicitOnly=true), p(','), allowEmpty=true) <~ p(')')
    ot <- opt(p(':') ~> typeParser)
    _  <- kw("=")
    b  <- exprParser
  } yield Function(i, ts.getOrElse(HSeq.fromSeq(Seq[Identifier]())), ps, ot, b)

  lazy val adtDefinitionParser: Parser[Sort] = {
    val constructorParser: Parser[Constructor] = for {
      i  <- identifierParser
      ps <- p('(') ~> hseqParser(bindingParser(explicitOnly=true), p(','), allowEmpty=true) <~ p(')')
    } yield Constructor(i, ps)

    for {
      _  <- kw("type")
      i  <- identifierParser
      ts <- opt(p('[') ~> hseqParser(identifierParser, p(',')) <~ p(']'))
      _  <- kw("=")
      cs <- hseqParser(constructorParser, operator("|"))
    } yield Sort(i, ts.getOrElse(HSeq.fromSeq(Seq[Identifier]())), cs)
  }

  def bindingParser(explicitOnly: Boolean=false): Parser[Binding] = holeParser.map(BindingHole(_)) | {

    def typeParserOf(id: Identifier): Parser[Type] = id match {
      case IdentifierHole(_) => typeParser
      case IdentifierName(name) => contextTypeParser(Some(name))
    }

    if (explicitOnly) {
      for {
        i <- identifierParser
        tpe <- p(':') ~> typeParserOf(i)
      } yield ExplicitValDef(i, tpe)
    }
    else {
      for {
        i <- identifierParser
        optTpe <- opt(p(':') ~> typeParserOf(i))
      } yield optTpe match {
        case None      => InferredValDef(i)
        case Some(tpe) => ExplicitValDef(i, tpe)
      }
    }
  }
}
