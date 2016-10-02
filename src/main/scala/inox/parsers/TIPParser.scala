/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package parsers

import _root_.smtlib.lexer._
import _root_.smtlib.parser.{Parser => SMTParser}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.parser.Terms.{Let => SMTLet, Forall => SMTForall, Identifier => SMTIdentifier, _}
import _root_.smtlib.theories._
import _root_.smtlib.theories.experimental._

import scala.collection.BitSet
import java.io.{Reader, File}

import utils._

import scala.language.implicitConversions

trait TIPParser {
  import inox.trees._

  private class PositionProvider(_reader: Reader, _file: Option[File]) {
    val (reader, file): (Reader, File) = _file match {
      case Some(file) => (_reader, file)
      case None =>
        val file = File.createTempFile("input", ".tip")
        val writer = new java.io.BufferedWriter(new java.io.FileWriter(file))

        val buffer = new Array[Char](1024)
        var count: Int = 0
        while ((count = _reader.read(buffer)) != -1) {
          writer.write(buffer, 0, count)
        }

        val reader = new java.io.BufferedReader(new java.io.FileReader(file))
        (reader, file)
    }

    private val fileLines: List[String] = scala.io.Source.fromFile(file).getLines.toList

    def get(line: Int, col: Int): OffsetPosition = {
      val point = fileLines.take(line).map(_.length).sum + col
      new OffsetPosition(line, col, point, file)
    }
  }

  class MissformedTIPException(reason: String, pos: Position)
    extends Exception("Missfomed TIP source @" + pos + ":\n" + reason)

  private class Parser(lex: Lexer, positions: PositionProvider) extends SMTParser(lex) {

    implicit def smtlibPositionToPosition(pos: _root_.smtlib.common.Position): Position = {
      positions.get(pos.line, pos.col)
    }

    private class Locals private(
      funs: Map[SSymbol, Identifier],
      adts: Map[SSymbol, Identifier],
      selectors: Map[SSymbol, Identifier],
      vars: Map[SSymbol, Variable],
      tps:  Map[SSymbol, TypeParameter],
      val symbols: Symbols) {

      def isADT(sym: SSymbol): Boolean = adts.isDefinedAt(sym)
      def lookupADT(sym: SSymbol): Option[Identifier] = adts.get(sym)
      def getADT(sym: SSymbol): Identifier = adts.get(sym).getOrElse {
        throw new MissformedTIPException("unknown ADT " + sym, sym.getPos)
      }

      def withADT(sym: SSymbol, id: Identifier): Locals = withADTs(Seq(sym -> id))
      def withADTs(seq: Seq[(SSymbol, Identifier)]): Locals =
        new Locals(funs, adts ++ seq, selectors, vars, tps, symbols)

      def isADTSelector(sym: SSymbol): Boolean = selectors.isDefinedAt(sym)
      def getADTSelector(sym: SSymbol): Identifier = selectors.get(sym).getOrElse {
        throw new MissformedTIPException("unknown ADT selector " + sym, sym.getPos)
      }

      def withADTSelectors(seq: Seq[(SSymbol, Identifier)]): Locals =
        new Locals(funs, adts, selectors ++ seq, vars, tps, symbols)

      def isGeneric(sym: SSymbol): Boolean = tps.isDefinedAt(sym)
      def lookupGeneric(sym: SSymbol): Option[TypeParameter] = tps.get(sym)
      def getGeneric(sym: SSymbol): TypeParameter = tps.get(sym).getOrElse {
        throw new MissformedTIPException("unknown generic type " + sym, sym.getPos)
      }

      def withGeneric(sym: SSymbol, tp: TypeParameter): Locals = withGenerics(Seq(sym -> tp))
      def withGenerics(seq: Seq[(SSymbol, TypeParameter)]): Locals =
        new Locals(funs, adts, selectors, vars, tps ++ seq, symbols)

      def withVariable(sym: SSymbol, v: Variable): Locals = withVariables(Seq(sym -> v))
      def withVariables(seq: Seq[(SSymbol, Variable)]): Locals =
        new Locals(funs, adts, selectors, vars ++ seq, tps, symbols)

      def isFunction(sym: SSymbol): Boolean = funs.isDefinedAt(sym)
      def getFunction(sym: SSymbol): Identifier = funs.get(sym).getOrElse {
        throw new MissformedTIPException("unknown function " + sym, sym.getPos)
      }

      def withFunction(sym: SSymbol, fd: FunDef): Locals = withFunctions(Seq(sym -> fd))
      def withFunctions(fds: Seq[(SSymbol, FunDef)]): Locals =
        new Locals(funs ++ fds.map(p => p._1 -> p._2.id), adts, selectors, vars, tps,
          symbols.withFunctions(fds.map(_._2)))

      def registerADT(adt: ADTDefinition): Locals = registerADTs(Seq(adt))
      def registerADTs(defs: Seq[ADTDefinition]): Locals =
        new Locals(funs, adts, selectors, vars, tps, symbols.withADTs(defs))
    }

    private object Locals {
      def empty = new Locals(Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, NoSymbols)
    }

    private def getIdentifier(sym: SSymbol): Identifier = {
      // TODO: check keywords!
      FreshIdentifier(sym.name)
    }

    def parseTIPScript: (InoxProgram, Expr) = {

      val ctx: InoxContext = InoxContext.empty
      var assertions: Seq[Expr] = Seq.empty
      implicit var locals: Locals = Locals.empty

      while (peekToken != null) {
        eat(Tokens.OParen)

        peekToken match {
          case Tokens.SymbolLit("assert-not") =>
            nextToken // eat the "assert-not" token
            assertions :+= Not(extractExpr(parseTerm))

          case Tokens.Token(Tokens.Assert) =>
            nextToken // eat the "assert" token
            assertions :+= extractExpr(parseTerm)

          case Tokens.Token(Tokens.DefineFun) | Tokens.Token(Tokens.DefineFunRec) =>
            // eats the "define-fun" or "define-fun-rec" token
            val isRec = nextToken == Tokens.Token(Tokens.DefineFunRec)
            val (tps, funDef) = getPeekToken.kind match {
              case Tokens.OParen =>
                eat(Tokens.OParen)
                eat(Tokens.Par)
                val tps = parseMany(parseSymbol _)
                val res = parseWithin(Tokens.OParen, Tokens.CParen)(parseFunDef _)
                eat(Tokens.CParen)
                (tps, res)

              case _ =>
                (Seq.empty[SSymbol], parseFunDef)
            }

            val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.getPos)))
            val fdsLocals = if (!isRec) tpsLocals else {
              tpsLocals.withFunction(funDef.name, extractSignature(funDef, tps)(tpsLocals))
            }
            val fd = extractFunction(funDef, tps)(fdsLocals)
            locals = locals.withFunction(funDef.name, fd)

          case Tokens.Token(Tokens.DefineFunsRec) =>
            nextToken // eat the "define-funs-rec" token
            val (funDec, funDecs) = parseOneOrMore(() => {
              eat(Tokens.OParen)
              val (tps, funDec) = getPeekToken.kind match {
                case Tokens.Par =>
                  eat(Tokens.Par)
                  val tps = parseMany(parseSymbol _)
                  val funDec = parseWithin(Tokens.OParen, Tokens.CParen)(parseFunDec _)
                  (tps -> funDec)

                case _ =>
                  (Seq.empty[SSymbol], parseFunDec)
              }
              eat(Tokens.CParen)
              (tps, funDec)
            })

            val (body, bodies) = parseOneOrMore(parseTerm _)
            assert(funDecs.size == bodies.size)

            val funDefs = ((funDec -> body) +: (funDecs zip bodies)).map {
              case ((tps, FunDec(name, params, returnSort)), body) =>
                tps -> SMTFunDef(name, params, returnSort, body)
            }

            val bodyLocals = locals.withFunctions(for ((tps, funDef) <- funDefs) yield {
              val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.getPos)))
              funDef.name -> extractSignature(funDef, tps)(tpsLocals)
            })

            locals = locals.withFunctions(for ((tps, funDef) <- funDefs) yield {
              val tpsLocals = bodyLocals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.getPos)))
              funDef.name -> extractFunction(funDef, tps)(tpsLocals)
            })

          case Tokens.Token(Tokens.DeclareDatatypes) =>
            nextToken // eat the "declare-datatypes" token
            val tps = parseMany(parseSymbol _)
            val datatypes = parseMany(parseDatatypes _)

            locals = locals.withADTs(datatypes
              .flatMap { case (sym, conss) => sym +: conss.map(_.sym) }
              .map(sym => sym -> getIdentifier(sym)))

            val adtLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.getPos)))
            for ((sym, conss) <- datatypes) {
              val children = for (Constructor(sym, fields) <- conss) yield {
                val id = locals.getADT(sym)
                val vds = fields.map { case (s, sort) =>
                  ValDef(getIdentifier(s), extractType(sort)(adtLocals)).setPos(s.getPos)
                }

                (id, vds)
              }

              val allVds: Set[ValDef] = children.flatMap(_._2).toSet
              val allTparams: Set[TypeParameter] = children.flatMap(_._2).toSet.flatMap {
                (vd: ValDef) => locals.symbols.typeParamsOf(vd.tpe): Set[TypeParameter]
              }

              val tparams: Seq[TypeParameterDef] = tps.flatMap { sym =>
                val tp = adtLocals.getGeneric(sym)
                if (allTparams(tp)) Some(TypeParameterDef(tp).setPos(sym.getPos)) else None
              }

              val parent = if (children.size > 1) {
                val id = adtLocals.getADT(sym)
                locals = locals.registerADT(
                  new ADTSort(id, tparams, children.map(_._1), Set.empty).setPos(sym.getPos))
                Some(id)
              } else {
                None
              }

              locals = locals.registerADTs((conss zip children).map { case (cons, (cid, vds)) =>
                new ADTConstructor(cid, tparams, parent, vds, Set.empty).setPos(cons.sym.getPos)
              }).withADTSelectors((conss zip children).flatMap { case (Constructor(_, fields), (_, vds)) =>
                (fields zip vds).map(p => p._1._1 -> p._2.id)
              })
            }

          case Tokens.Token(Tokens.DeclareConst) =>
            nextToken // eat the "declare-const" token
            val sym = parseSymbol
            val sort = parseSort
            locals = locals.withVariable(sym,
              Variable(getIdentifier(sym), extractType(sort)).setPos(sym.getPos))

          case Tokens.Token(Tokens.DeclareSort) =>
            nextToken // eat the "declare-const" token
            val sym = parseSymbol
            val arity = parseNumeral.value.toInt
            locals = if (arity == 0) {
              locals.withGeneric(sym, TypeParameter.fresh(sym.name))
            } else {
              val id = getIdentifier(sym)
              locals.withADT(sym, id).registerADT {
                val tparams = List.range(0, arity).map {
                  i => TypeParameterDef(TypeParameter.fresh("A" + i).setPos(sym.getPos)).setPos(sym.getPos)
                }
                val field = ValDef(FreshIdentifier("val"), IntegerType).setPos(sym.getPos)

                new ADTConstructor(id, tparams, None, Seq(field), Set.empty)
              }
            }

          case Tokens.Token(Tokens.CheckSat) =>
            // TODO: what do I do with this??

          case token =>
            throw new MissformedTIPException("unknown TIP command " + token, token.getPos)
        }

        eat(Tokens.CParen)
      }

      val expr: Expr = locals.symbols.andJoin(assertions)
      val program = InoxProgram(ctx, locals.symbols)
      (program, expr)
    }

    override protected def parseTermWithoutParens: Term = getPeekToken match {
      case Tokens.SymbolLit("lambda") =>
        nextToken // eat the "lambda" token
        val vars = parseMany(parseSortedVar _)
        val term = parseTerm
        FunctionApplication(
          QualifiedIdentifier(SMTIdentifier(SSymbol("lambda"))),
          vars.map { case SortedVar(sym, sort) => QualifiedIdentifier(SMTIdentifier(sym), Some(sort)) } :+ term
        )

      case _ => super.parseTermWithoutParens
    }

    private def extractSignature(fd: SMTFunDef, tps: Seq[SSymbol])(implicit locals: Locals): FunDef = {
      assert(!locals.isFunction(fd.name))
      val id = getIdentifier(fd.name)
      val tparams = tps.map(sym => TypeParameterDef(locals.getGeneric(sym)).setPos(sym.getPos))

      val params = fd.params.map { case SortedVar(s, sort) =>
        ValDef(getIdentifier(s), extractType(sort)).setPos(s.getPos)
      }

      val returnType = extractType(fd.returnSort)
      val body = Choose(ValDef(FreshIdentifier("res"), returnType), BooleanLiteral(true))

      new FunDef(id, tparams, params, returnType, body, Set.empty).setPos(fd.name.getPos)
    }

    private def extractFunction(fd: SMTFunDef, tps: Seq[SSymbol])(implicit locals: Locals): FunDef = {
      val sig = if (locals.isFunction(fd.name)) {
        locals.symbols.getFunction(locals.getFunction(fd.name))
      } else {
        extractSignature(fd, tps)
      }

      val bodyLocals = locals
        .withVariables((fd.params zip sig.params).map(p => p._1.name -> p._2.toVariable))
        .withFunctions(if (locals.isFunction(fd.name)) Seq(fd.name -> sig) else Seq.empty)

      val fullBody = extractExpr(fd.body)(bodyLocals)

      new FunDef(sig.id, sig.tparams, sig.params, sig.returnType, fullBody, Set.empty).setPos(fd.name.getPos)
    }

    private def isInstanceOfSymbol(sym: SSymbol)(implicit locals: Locals): Option[Identifier] = {
      if (sym.name.startsWith("is-")) {
        val adtSym = SSymbol(sym.name.split("-").tail.mkString("-"))
        locals.lookupADT(adtSym)
      } else {
        None
      }
    }

    private def typeADTConstructor(id: Identifier, superType: Type)(implicit locals: Locals): ADTType = {
      val tcons = locals.symbols.getADT(id).typed(locals.symbols).toConstructor
      val troot = tcons.root.toType
      locals.symbols.canBeSupertypeOf(troot, superType) match {
        case Some(tmap) => locals.symbols.instantiateType(tcons.toType, tmap).asInstanceOf[ADTType]
        case None => throw new MissformedTIPException(
          "cannot construct full typing for " + tcons,
          superType.getPos
        )
      }
    }

    private def instantiateTypeParams(tps: Seq[TypeParameterDef], formals: Seq[Type], actuals: Seq[Type])
                                     (implicit locals: Locals): Seq[Type] = {
      assert(formals.size == actuals.size)

      import locals.symbols._
      val formal = bestRealType(tupleTypeWrap(formals))
      val actual = bestRealType(tupleTypeWrap(actuals))
      canBeSupertypeOf(formal, actual) match {
        case Some(tmap) => tps.map(tpd => tmap.getOrElse(tpd.tp, tpd.tp))
        case None => throw new MissformedTIPException(
          s"could not instantiate $tps in $formals given $actuals",
          actuals.headOption.map(_.getPos).getOrElse(NoPosition)
        )
      }
    }

    private def wrapAsInstanceOf(formals: Seq[Type], exprs: Seq[Expr])(implicit locals: Locals): Seq[Expr] = {
      (formals zip exprs).map { case (tpe, e) =>
        (tpe, e.getType(locals.symbols)) match {
          case (tp1: ADTType, tp2: ADTType) if tp1 != tp2 && locals.symbols.isSubtypeOf(tp1, tp2) =>
            AsInstanceOf(e, tp1)
          case _ => e
        }
      }
    }

    private def extractExpr(term: Term)(implicit locals: Locals): Expr = (term match {
      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("assume")), None), Seq(pred, body)) =>
        Assume(extractExpr(pred), extractExpr(body))

      case SMTLet(binding, bindings, term) =>
        var locs = locals
        val mapping = for (VarBinding(name, term) <- (binding +: bindings)) yield {
          val e = extractExpr(term)(locs)
          val tpe = e.getType(locs.symbols)
          val vd = ValDef(getIdentifier(name), tpe).setPos(name.getPos)
          locs = locs.withVariable(name, vd.toVariable)
          vd -> e
        }

        mapping.foldRight(extractExpr(term)(locs)) { case ((vd, e), body) => Let(vd, e, body).setPos(vd.getPos) }

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("@")), None), fun +: args) =>
        Application(extractExpr(fun), args.map(extractExpr))

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("lambda")), None), args :+ body) =>
        val (vds, bindings) = args.map { case QualifiedIdentifier(SimpleIdentifier(s), Some(sort)) =>
          val vd = ValDef(getIdentifier(s), extractType(sort)).setPos(s.getPos)
          (vd, s -> vd.toVariable)
        }.unzip

        Lambda(vds, extractExpr(body)(locals.withVariables(bindings)))

      case SMTForall(sv, svs, term) =>
        val (vds, bindings) = (sv +: svs).map { case SortedVar(s, sort) =>
          val vd = ValDef(getIdentifier(s), extractType(sort)).setPos(s.getPos)
          (vd, s -> vd.toVariable)
        }.unzip

        Forall(vds, extractExpr(term)(locals.withVariables(bindings)))

      case Exists(sv, svs, term) =>
        val (vds, bindings) = (sv +: svs).map { case SortedVar(s, sort) =>
          val vd = ValDef(getIdentifier(s), extractType(sort)).setPos(s.getPos)
          (vd, s -> vd.toVariable)
        }.unzip

        val body = Not(extractExpr(term)(locals.withVariables(bindings))).setPos(term.getPos)
        Forall(vds, body)

      case Core.ITE(cond, thenn, elze) =>
        IfExpr(extractExpr(cond), extractExpr(thenn), extractExpr(elze))

      case SNumeral(n) =>
        IntegerLiteral(n)

      // TODO: hexadecimal case
      //case SHexadecimal(value) => BVLiteral()

      case SBinary(bs) =>
        BVLiteral(BitSet.empty ++ bs.reverse.zipWithIndex.collect { case (true, i) => i }, bs.size)

      case SDecimal(value) =>
        FractionLiteral(
          value.bigDecimal.movePointRight(value.scale).toBigInteger,
          BigInt(10).pow(value.scale))

      case SString(value) =>
        StringLiteral(value)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args)
      if locals.isADT(sym) =>
        val es = args.map(extractExpr)
        val cons = locals.symbols.getADT(locals.getADT(sym)).asInstanceOf[ADTConstructor]
        val tps = instantiateTypeParams(cons.tparams, cons.fields.map(_.tpe), es.map(_.getType(locals.symbols)))
        val tcons = cons.typed(tps)(locals.symbols)
        ADT(tcons.toType, wrapAsInstanceOf(tcons.fieldsTypes, es))

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args)
      if locals.isFunction(sym) =>
        val es = args.map(extractExpr)
        val fd = locals.symbols.getFunction(locals.getFunction(sym))
        val tps = instantiateTypeParams(fd.tparams, fd.params.map(_.tpe), es.map(_.getType(locals.symbols)))
        val tfd = fd.typed(tps)(locals.symbols)
        tfd.applied(wrapAsInstanceOf(tfd.params.map(_.tpe), es))

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), Seq(term))
      if isInstanceOfSymbol(sym).isDefined =>
        val e = extractExpr(term)
        val tpe = typeADTConstructor(isInstanceOfSymbol(sym).get, e.getType(locals.symbols))
        IsInstanceOf(e, tpe)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), Seq(term))
      if locals.isADTSelector(sym) =>
        ADTSelector(extractExpr(term), locals.getADTSelector(sym))

      case Core.Equals(e1, e2) => Equals(extractExpr(e1), extractExpr(e2))
      case Core.And(es @ _*) => And(es.map(extractExpr))
      case Core.Or(es @ _*) => Or(es.map(extractExpr))
      case Core.Implies(e1, e2) => Implies(extractExpr(e1), extractExpr(e2))
      case Core.Not(e) => Not(extractExpr(e))

      case Core.True() => BooleanLiteral(true)
      case Core.False() => BooleanLiteral(false)

      case Strings.Length(s) => StringLength(extractExpr(s))
      case Strings.Concat(e1, e2, es @ _*) =>
        es.foldLeft(StringConcat(extractExpr(e1), extractExpr(e2)).setPos(term.getPos)) {
          (c,e) => StringConcat(c, extractExpr(e)).setPos(term.getPos)
        }

      case Strings.Substring(e, start, end) =>
        SubString(extractExpr(e), extractExpr(start), extractExpr(end))

      /* Ints extractors cover the Reals operations as well */

      case Ints.Neg(e) => UMinus(extractExpr(e))
      case Ints.Add(e1, e2) => Plus(extractExpr(e1), extractExpr(e2))
      case Ints.Sub(e1, e2) => Minus(extractExpr(e1), extractExpr(e2))
      case Ints.Mul(e1, e2) => Times(extractExpr(e1), extractExpr(e2))
      case Ints.Div(e1, e2) => Division(extractExpr(e1), extractExpr(e2))
      case Ints.Mod(e1, e2) => Modulo(extractExpr(e1), extractExpr(e2))
      case Ints.Abs(e) =>
        val ie = extractExpr(e)
        IfExpr(
          LessThan(ie, IntegerLiteral(BigInt(0)).setPos(term.getPos)).setPos(term.getPos),
          UMinus(ie).setPos(term.getPos),
          ie
        )

      case Ints.LessThan(e1, e2) => LessThan(extractExpr(e1), extractExpr(e2))
      case Ints.LessEquals(e1, e2) => LessEquals(extractExpr(e1), extractExpr(e2))
      case Ints.GreaterThan(e1, e2) => GreaterThan(extractExpr(e1), extractExpr(e2))
      case Ints.GreaterEquals(e1, e2) => GreaterEquals(extractExpr(e1), extractExpr(e2))

      case FixedSizeBitVectors.Not(e) => BVNot(extractExpr(e))
      case FixedSizeBitVectors.Neg(e) => UMinus(extractExpr(e))
      case FixedSizeBitVectors.And(e1, e2) => BVAnd(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.Or(e1, e2) => BVOr(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.XOr(e1, e2) => BVXor(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.Add(e1, e2) => Plus(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.Sub(e1, e2) => Minus(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.Mul(e1, e2) => Times(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.SDiv(e1, e2) => Division(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.SRem(e1, e2) => Remainder(extractExpr(e1), extractExpr(e2))

      case FixedSizeBitVectors.SLessThan(e1, e2) => LessThan(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.SLessEquals(e1, e2) => LessEquals(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.SGreaterThan(e1, e2) => GreaterThan(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.SGreaterEquals(e1, e2) => GreaterEquals(extractExpr(e1), extractExpr(e2))

      case FixedSizeBitVectors.ShiftLeft(e1, e2) => BVShiftLeft(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.AShiftRight(e1, e2) => BVAShiftRight(extractExpr(e1), extractExpr(e2))
      case FixedSizeBitVectors.LShiftRight(e1, e2) => BVLShiftRight(extractExpr(e1), extractExpr(e2))

      case ArraysEx.Select(e1, e2) => MapApply(extractExpr(e1), extractExpr(e2))
      case ArraysEx.Store(e1, e2, e3) => MapUpdated(extractExpr(e1), extractExpr(e2), extractExpr(e3))
      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("const")), Some(sort)), Seq(dflt)) =>
        FiniteMap(Seq.empty, extractExpr(dflt), extractType(sort))

      case Sets.Union(e1, e2) => SetUnion(extractExpr(e1), extractExpr(e2))
      case Sets.Intersection(e1, e2) => SetIntersection(extractExpr(e1), extractExpr(e2))
      case Sets.Setminus(e1, e2) => SetDifference(extractExpr(e1), extractExpr(e2))
      case Sets.Member(e1, e2) => ElementOfSet(extractExpr(e1), extractExpr(e2))
      case Sets.Subset(e1, e2) => SubsetOf(extractExpr(e1), extractExpr(e2))

      case Sets.Singleton(e) =>
        val elem = extractExpr(e)
        FiniteSet(Seq(elem), locals.symbols.bestRealType(elem.getType(locals.symbols)))

      case Sets.Insert(set, es @ _*) =>
        es.foldLeft(extractExpr(set))((s,e) => SetAdd(s, extractExpr(e)))

      // TODO: bags

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("match")), None), s +: cases) =>
        val scrut = extractExpr(s)
        val matchCases: Seq[(Option[Expr], Expr)] = cases.map {
          case FunctionApplication(
            QualifiedIdentifier(SimpleIdentifier(SSymbol("case")), None),
            Seq(pat, term)
          ) => pat match {
            case QualifiedIdentifier(SimpleIdentifier(SSymbol("default")), None) =>
              (None, extractExpr(term))

            case QualifiedIdentifier(SimpleIdentifier(sym), None) =>
              val id = locals.getADT(sym)
              val tpe = typeADTConstructor(id, scrut.getType(locals.symbols))
              (Some(IsInstanceOf(scrut, tpe).setPos(sym.getPos)), extractExpr(term))

            case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args) =>
              val id = locals.getADT(sym)
              val tpe = typeADTConstructor(id, scrut.getType(locals.symbols))

              val tcons = tpe.getADT(locals.symbols).toConstructor
              val bindings = (tcons.fields zip args).map {
                case (vd, QualifiedIdentifier(SimpleIdentifier(sym), None)) =>
                  (sym, vd.id, vd.freshen)
              }

              val expr = extractExpr(term)(locals.withVariables(bindings.map(p => p._1 -> p._3.toVariable)))
              val fullExpr = bindings.foldRight(expr) { case ((s, id, vd), e) =>
                val selector = ADTSelector(AsInstanceOf(scrut, tpe).setPos(s.getPos), id).setPos(s.getPos)
                Let(vd, selector, e).setPos(s.getPos)
              }

              (Some(IsInstanceOf(scrut, tpe).setPos(sym.getPos)), fullExpr)

            case _ => throw new MissformedTIPException("unexpected match pattern " + pat, pat.getPos)
          }

          case cse => throw new MissformedTIPException("unexpected match case " + cse, cse.getPos)
        }

        val (withCond, withoutCond) = matchCases.partition(_._1.isDefined)
        val (ifs, last) = if (withoutCond.size > 1) {
          throw new MissformedTIPException("unexpected multiple defaults in " + term, term.getPos)
        } else if (withoutCond.size == 1) {
          (withCond.map(p => p._1.get -> p._2), withoutCond.head._2)
        } else {
          val wc = withCond.map(p => p._1.get -> p._2)
          (wc.init, wc.last._2)
        }

        ifs.foldRight(last) { case ((cond, body), elze) => IfExpr(cond, body, elze).setPos(cond.getPos) }

    }).setPos(term.getPos)

    private def extractType(sort: Sort)(implicit locals: Locals): Type = (sort match {
      case Sort(SMTIdentifier(SSymbol("bitvector"), Seq(SNumeral(n))), Seq()) => BVType(n.toInt)
      case Sort(SimpleIdentifier(SSymbol("Bool")), Seq()) => BooleanType
      case Sort(SimpleIdentifier(SSymbol("Int")), Seq()) => IntegerType

      case Sort(SimpleIdentifier(SSymbol("Array")), Seq(from, to)) =>
        MapType(extractType(from), extractType(to))

      case Sort(SimpleIdentifier(SSymbol("Set")), Seq(base)) =>
        SetType(extractType(base))

      case Sort(SimpleIdentifier(SSymbol("Bag")), Seq(base)) =>
        BagType(extractType(base))

      case Sort(SimpleIdentifier(SSymbol("=>")), params :+ res) =>
        FunctionType(params.map(extractType), extractType(res))

      case Sort(SimpleIdentifier(sym), Seq()) if locals.isGeneric(sym) =>
        locals.getGeneric(sym)

      case Sort(SimpleIdentifier(sym), tps) if locals.isADT(sym) =>
        ADTType(locals.getADT(sym), tps.map(extractType))

      case _ => throw new MissformedTIPException("unexpected sort: " + sort, sort.id.symbol.getPos)
    }).setPos(sort.id.symbol.getPos)
  }
}
