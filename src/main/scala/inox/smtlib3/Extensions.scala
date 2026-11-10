/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package smtlib3

import smtlib.printer._
import smtlib.trees.Terms._
import smtlib.trees.Commands._
import smtlib.trees.TreeTransformer
import smtlib.lexer.{Tokens => LT}
import smtlib.common.Position
import smtlib.extensions.tip.{Tokens => TipTokens}
import smtlib.extensions.tip.Terms.{Match, Case, Pattern, Default, CaseObject, CaseClass}

import inox.tip.{TipLexer, TipParser, Tokens => InoxTipTokens}

import scala.collection.mutable.ListBuffer

/** Syntax added by SMT-LIB 3 on top of the TIP/SMT-LIB 2 syntax understood by [[inox.tip]].
  *
  * See the SMT-LIB 3 proposal at https://smt-lib.org/version3.shtml.
  */
object Tokens {
  import LT.ReservedWord

  case object DeclareTypeVar extends ReservedWord
  case object DeclareType extends ReservedWord
  case object DefineType extends ReservedWord
  case object DefineConst extends ReservedWord
  case object DefineConstRec extends ReservedWord
  case object DeclareDatatype extends ReservedWord
  case object DatatypeEquality extends ReservedWord
}

object Terms {

  /** A type, which SMT-LIB 3 parses as a term since types can depend on values.
    *
    * Sorts that are also SMT-LIB 2 sorts are kept as plain [[Sort]]s, so only types that
    * mention values, such as `(BitVec 32)` or `(-> (! Int :var n) (Vec n))`, use this class.
    */
  final class TermSort(val term: Term) extends Sort(Identifier(SSymbol("$type-term")), Seq.empty) {
    override def equals(that: Any): Boolean = that match {
      case ts: TermSort => term == ts.term
      case _ => false
    }
    override def hashCode: Int = term.hashCode
    override def toString: String = s"TermSort($term)"
  }

  object TermSort {
    def apply(term: Term): Sort = term match {
      case QualifiedIdentifier(id, None) => Sort(id).setPos(term)
      case FunctionApplication(QualifiedIdentifier(id, None), args) =>
        val sorts = args.map(apply)
        if (sorts.exists(_.isInstanceOf[TermSort])) new TermSort(term).setPos(term)
        else Sort(id, sorts).setPos(term)
      case _ => new TermSort(term).setPos(term)
    }

    def toTerm(sort: Sort): Term = sort match {
      case ts: TermSort => ts.term
      case Sort(id, Seq()) => QualifiedIdentifier(id).setPos(sort)
      case Sort(id, sorts) => FunctionApplication(QualifiedIdentifier(id).setPos(sort), sorts.map(toTerm)).setPos(sort)
    }
  }

  /** An annotated term `(! t :var x :implicit :restrict p ...)` that binds a variable,
    * as used in dependent function types and predicate subtypes. */
  case class VarAnnotation(term: Term, name: Option[SSymbol], isImplicit: Boolean,
                           restrictions: Seq[Term], attributes: Seq[Attribute]) extends TermExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(! ")
      ctx.print(term)
      name.foreach { n => ctx.print(" :var "); ctx.print(n) }
      if (isImplicit) ctx.print(" :implicit")
      restrictions.foreach { r => ctx.print(" :restrict "); ctx.print(r) }
      attributes.foreach { a => ctx.print(" "); ctx.print(a) }
      ctx.print(")")
    }
  }

  /** A higher-order binder application such as `(forall p)` or `(exists (lambda ((x Int)) ...))`. */
  case class BinderApplication(binder: String, body: Term) extends TermExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(" + binder + " ")
      ctx.print(body)
      ctx.print(")")
    }
  }
}

object Commands {
  import Terms._

  private def unsupported = throw new UnsupportedOperationException("SMT-LIB 3 commands can't be transformed")

  case class DeclareTypeVar(name: SSymbol) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(declare-type-var ")
      ctx.print(name)
      ctx.print(")\n")
    }
    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = unsupported
  }

  /** `(declare-type S (Type ... Type))` */
  case class DeclareType(name: SSymbol, kinds: Seq[Sort]) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(declare-type ")
      ctx.print(name)
      ctx.printNary(kinds, " (", " ", "))\n")
    }
    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = unsupported
  }

  /** A parameter of `define-type`: either a type parameter, or a value parameter `(! T :var x)`. */
  sealed trait TypeDefParam
  case class TypeParam(name: SSymbol) extends TypeDefParam
  case class ValueParam(annotation: VarAnnotation) extends TypeDefParam

  /** `(define-type S (params) body)`, which generalizes `define-sort` to value parameters. */
  case class DefineType(name: SSymbol, params: Seq[TypeDefParam], body: Sort) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(define-type ")
      ctx.print(name)
      ctx.print(" (")
      printParams(ctx, params)
      ctx.print(") ")
      ctx.print(body)
      ctx.print(")\n")
    }
    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = unsupported
  }

  /** `(define-const c T t)` and `(define-const-rec c T t)` */
  case class DefineConst(name: SSymbol, sort: Sort, body: Term, isRec: Boolean) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print(if (isRec) "(define-const-rec " else "(define-const ")
      ctx.print(name)
      ctx.print(" ")
      ctx.print(sort)
      ctx.print(" ")
      ctx.print(body)
      ctx.print(")\n")
    }
    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = unsupported
  }

  private def printParams(ctx: PrintingContext, params: Seq[TypeDefParam]): Unit =
    ctx.printNary[TypeDefParam](params, {
      case TypeParam(n) => ctx.print(n)
      case ValueParam(a) => ctx.print(a)
    }, "", " ", "")

  /** A constructor whose field types may refer to its previous fields, and which may restrict its
    * fields with `:restrict` annotations. */
  case class ConstructorDec(sym: SSymbol, fields: Seq[(SSymbol, Sort)], restrictions: Seq[Term])

  /** A datatype with type parameters. */
  case class DatatypeDec(name: SSymbol, params: Seq[SSymbol], constructors: Seq[ConstructorDec])

  /** SMT-LIB 2.6+ datatype declarations, where each datatype has its own parameters. */
  case class DeclareDatatypesWithPars(datatypes: Seq[DatatypeDec]) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(declare-datatypes (")
      ctx.print(datatypes.map(d => s"(${d.name.name} ${d.params.size})").mkString(" "))
      ctx.print(") (")
      ctx.printNary[DatatypeDec](datatypes, { d =>
        if (d.params.nonEmpty) {
          ctx.printNary(d.params, "(par (", " ", ") ")
        }
        ctx.printNary[ConstructorDec](d.constructors, { c =>
          ctx.print("(")
          ctx.print(c.sym)
          for ((s, sort) <- c.fields) {
            ctx.print(" (")
            ctx.print(s)
            ctx.print(" ")
            ctx.print(sort)
            ctx.print(")")
          }
          for (r <- c.restrictions) {
            ctx.print(" :restrict ")
            ctx.print(r)
          }
          ctx.print(")")
        }, "(", " ", ")")
        if (d.params.nonEmpty) ctx.print(")")
      }, "", " ", "")
      ctx.print("))\n")
    }
    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = unsupported
  }

  /** `(datatype-equality S f)`: two values of the datatype `S` are equal when `f` holds of them,
    * where `f` takes two values of `S` (with the type parameters of `S`). */
  case class DatatypeEquality(sort: SSymbol, function: SSymbol) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(datatype-equality ")
      ctx.print(sort)
      ctx.print(" ")
      ctx.print(function)
      ctx.print(")\n")
    }
    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = unsupported
  }
}

/** Reads `→` as `->`, so that the lexer accepts both spellings of the function type constructor. */
class ArrowReader(underlying: java.io.Reader) extends java.io.Reader {
  private var pending: Int = -1

  override def read(): Int = {
    if (pending != -1) {
      val c = pending
      pending = -1
      c
    } else underlying.read() match {
      case '→' => pending = '>'; '-'
      case c => c
    }
  }

  override def read(cbuf: Array[Char], off: Int, len: Int): Int = {
    if (len == 0) return 0
    var i = 0
    var eof = false
    while (i < len && !eof) {
      val c = read()
      if (c == -1) eof = true
      else {
        cbuf(off + i) = c.toChar
        i += 1
        // stop at line ends so that interactive inputs aren't blocked on
        if (c == '\n' && pending == -1) eof = true
      }
    }
    if (i == 0) -1 else i
  }

  override def close(): Unit = underlying.close()
}

class SMTLIB3Lexer(reader: java.io.Reader) extends TipLexer(reader) {
  import LT.Token

  override protected def toReserved(s: String): Option[Token] = s match {
    case "declare-type-var" => Some(Token(Tokens.DeclareTypeVar))
    case "declare-type" => Some(Token(Tokens.DeclareType))
    case "define-type" => Some(Token(Tokens.DefineType))
    case "define-const" => Some(Token(Tokens.DefineConst))
    case "define-const-rec" => Some(Token(Tokens.DefineConstRec))
    case "declare-datatype" => Some(Token(Tokens.DeclareDatatype))
    case "datatype-equality" => Some(Token(Tokens.DatatypeEquality))
    case _ => super.toReserved(s)
  }
}

class SMTLIB3Parser(lexer: SMTLIB3Lexer) extends TipParser(lexer) {
  import Terms._
  import Commands._

  /** Types are terms in SMT-LIB 3, e.g. `(BitVec n)` or `(-> (! Int :var n) (BitVec n))`. */
  override def parseSort: Sort = TermSort(parseTerm)

  private def isSymbol(kind: LT.TokenKind): Boolean = kind == LT.SymbolLitKind

  /** Parses the rest of a binder `(b ...)` after `b`, in either of its SMT-LIB 3 forms:
    * binder sugar `(b ((x T) ...) body)`, or a higher-order application `(b f)`. */
  private def parseBinder(name: String, startPos: Position)(sugar: (Seq[SortedVar], Term) => Term): Term = {
    getPeekToken.kind match {
      case LT.OParen =>
        val pos = getPeekToken.getPos
        eat(LT.OParen)
        getPeekToken.kind match {
          case LT.OParen | LT.CParen =>
            val vars = parseUntil(LT.CParen)(() => parseSortedVar)
            val body = parseTerm
            sugar(vars, body)
          case _ =>
            val fun = parseTermWithoutParens(pos).setPos(pos)
            eat(LT.CParen)
            BinderApplication(name, fun)
        }
      case _ =>
        BinderApplication(name, parseTerm)
    }
  }

  private def parsePattern: Pattern = getPeekToken.kind match {
    case LT.OParen =>
      val (sym, binders) = parseOneOrMore(() => parseSymbol)
      CaseClass(sym, binders)
    case TipTokens.Default =>
      eat(TipTokens.Default)
      Default
    case _ =>
      val sym = parseSymbol
      if (sym.name == "_") Default else CaseObject(sym)
  }

  /** The rest of a TIP-style case `(case pattern rhs)` after its opening parenthesis. */
  private def parseTipCase: Case = {
    eat(TipTokens.Case)
    val pattern = parsePattern
    val rhs = parseTerm
    eat(LT.CParen)
    Case(pattern, rhs)
  }

  override protected def parseTermWithoutParens(startPos: Position): Term = getPeekToken.kind match {
    case LT.ExclamationMark =>
      eat(LT.ExclamationMark)
      val term = parseTerm
      var name: Option[SSymbol] = None
      var isImplicit = false
      val restrictions = new ListBuffer[Term]
      val attributes = new ListBuffer[Attribute]
      while (getPeekToken.kind != LT.CParen) {
        getPeekToken match {
          case LT.Keyword("var") =>
            nextToken()
            name = Some(parseSymbol)
          case LT.Keyword("implicit") =>
            nextToken()
            isImplicit = true
          case LT.Keyword("restrict") =>
            nextToken()
            restrictions += parseTerm
          case _ =>
            attributes += parseAttribute
        }
      }
      if (name.isEmpty && !isImplicit && restrictions.isEmpty && attributes.nonEmpty) {
        AnnotatedTerm(term, attributes.head, attributes.tail.toSeq)
      } else {
        VarAnnotation(term, name, isImplicit, restrictions.toSeq, attributes.toSeq)
      }

    case LT.Forall =>
      eat(LT.Forall)
      parseBinder("forall", startPos) {
        case (v +: vs, body) => Forall(v, vs, body)
        case (_, body) => body
      }

    case LT.Exists =>
      eat(LT.Exists)
      parseBinder("exists", startPos) {
        case (v +: vs, body) => Exists(v, vs, body)
        case (_, body) => body
      }

    case TipTokens.Match =>
      eat(TipTokens.Match)
      val scrut = parseTerm
      eat(LT.OParen)
      val cases = getPeekToken.kind match {
        case TipTokens.Case =>
          // TIP syntax: (match t (case p1 t1) (case p2 t2) ...)
          val first = parseTipCase
          first +: parseUntil(LT.CParen, eatEnd = false) { () =>
            eat(LT.OParen)
            parseTipCase
          }
        case _ =>
          // SMT-LIB 2.6+ syntax: (match t ((p1 t1) (p2 t2) ...))
          parseUntil(LT.CParen) { () =>
            eat(LT.OParen)
            val pattern = parsePattern
            val rhs = parseTerm
            eat(LT.CParen)
            Case(pattern, rhs)
          }
      }
      Match(scrut, cases)

    case _ => super.parseTermWithoutParens(startPos)
  }

  /** A type parameter `X`, or a value parameter `(! T :var n)`. */
  private def parseTypeDefParam: TypeDefParam = {
    if (isSymbol(getPeekToken.kind)) TypeParam(parseSymbol)
    else {
      val token = getPeekToken
      parseTerm match {
        case va @ VarAnnotation(_, Some(_), _, _, _) => ValueParam(va)
        case _ => throw new smtlib.parser.Parser.UnexpectedTokenException(token, Seq(LT.SymbolLitKind))
      }
    }
  }

  /** `(c (f1 T1) ... :restrict p ...)` */
  private def parseConstructorDec: ConstructorDec = {
    eat(LT.OParen)
    val sym = parseSymbol
    val fields = new ListBuffer[(SSymbol, Sort)]
    val restrictions = new ListBuffer[Term]
    while (getPeekToken.kind != LT.CParen) {
      getPeekToken match {
        case LT.Keyword("restrict") =>
          nextToken()
          restrictions += parseTerm
        case _ =>
          eat(LT.OParen)
          val name = parseSymbol
          val sort = parseSort
          eat(LT.CParen)
          fields += name -> sort
      }
    }
    eat(LT.CParen)
    ConstructorDec(sym, fields.toSeq, restrictions.toSeq)
  }

  /** `((c1 ...) (c2 ...))` or `(par (X ...) ((c1 ...) ...))` */
  private def parseDatatypeDec(name: SSymbol): DatatypeDec = {
    eat(LT.OParen)
    getPeekToken.kind match {
      case LT.Par =>
        eat(LT.Par)
        val params = parseMany(() => parseSymbol)
        val conss = parseMany(() => parseConstructorDec)
        eat(LT.CParen)
        DatatypeDec(name, params, conss)
      case _ =>
        val conss = parseUntil(LT.CParen)(() => parseConstructorDec)
        DatatypeDec(name, Seq.empty, conss)
    }
  }

  override protected def parseCommandWithoutParens: Command = getPeekToken.kind match {
    case Tokens.DeclareTypeVar =>
      eat(Tokens.DeclareTypeVar)
      DeclareTypeVar(parseSymbol)

    case Tokens.DeclareType =>
      eat(Tokens.DeclareType)
      val name = parseSymbol
      val kinds = parseMany(() => parseSort)
      DeclareType(name, kinds)

    case Tokens.DefineType =>
      eat(Tokens.DefineType)
      val name = parseSymbol
      val params = parseMany(() => parseTypeDefParam)
      val body = parseSort
      DefineType(name, params, body)

    case Tokens.DefineConst | Tokens.DefineConstRec =>
      val isRec = nextToken().kind == Tokens.DefineConstRec
      val name = parseSymbol
      val sort = parseSort
      val body = parseTerm
      DefineConst(name, sort, body, isRec)

    case Tokens.DatatypeEquality =>
      eat(Tokens.DatatypeEquality)
      val sort = parseSymbol
      DatatypeEquality(sort, parseSymbol)

    case Tokens.DeclareDatatype =>
      eat(Tokens.DeclareDatatype)
      val name = parseSymbol
      DeclareDatatypesWithPars(Seq(parseDatatypeDec(name)))

    case LT.DeclareDatatypes =>
      eat(LT.DeclareDatatypes)
      eat(LT.OParen)
      getPeekToken.kind match {
        case LT.OParen =>
          // SMT-LIB 2.6+ syntax: (declare-datatypes ((S1 n1) ...) (dec1 ...))
          val names = parseUntil(LT.CParen) { () =>
            eat(LT.OParen)
            val name = parseSymbol
            parseNumeral
            eat(LT.CParen)
            name
          }
          eat(LT.OParen)
          val decs = names.map(parseDatatypeDec)
          eat(LT.CParen)
          DeclareDatatypesWithPars(decs)

        case _ =>
          // TIP syntax: (declare-datatypes (X ...) ((S c1 ...) ...))
          val tps = parseUntil(LT.CParen)(() => parseSymbol)
          val datatypes = parseMany(() => parseDatatypes)
          smtlib.extensions.tip.Commands.DeclareDatatypesPar(tps, datatypes)
      }

    case _ => super.parseCommandWithoutParens
  }
}
