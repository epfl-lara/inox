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
  val trees: ast.Trees
  import trees._

  def parse(file: File): (Symbols, Expr) = {
    val pos = new PositionProvider(new java.io.BufferedReader(new java.io.FileReader(file)), Some(file))
    val parser = new Parser(new Lexer(pos.reader), pos)
    parser.parseTIPScript
  }

  def parse(reader: Reader): (Symbols, Expr) = {
    val pos = new PositionProvider(reader, None)
    val parser = new Parser(new Lexer(pos.reader), pos)
    parser.parseTIPScript
  }

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

  protected class Parser(lex: Lexer, positions: PositionProvider) extends SMTParser(lex) {

    implicit def smtlibPositionToPosition(pos: Option[_root_.smtlib.common.Position]): Position = {
      pos.map(p => positions.get(p.line, p.col)).getOrElse(NoPosition)
    }

    protected class Locals (
      funs: Map[SSymbol, Identifier],
      adts: Map[SSymbol, Identifier],
      selectors: Map[SSymbol, Identifier],
      vars: Map[SSymbol, Variable],
      tps:  Map[SSymbol, TypeParameter],
      val symbols: Symbols) {

      def isADT(sym: SSymbol): Boolean = adts.isDefinedAt(sym)
      def lookupADT(sym: SSymbol): Option[Identifier] = adts.get(sym)
      def getADT(sym: SSymbol): Identifier = adts.get(sym).getOrElse {
        throw new MissformedTIPException("unknown ADT " + sym, sym.optPos)
      }

      def withADT(sym: SSymbol, id: Identifier): Locals = withADTs(Seq(sym -> id))
      def withADTs(seq: Seq[(SSymbol, Identifier)]): Locals =
        new Locals(funs, adts ++ seq, selectors, vars, tps, symbols)

      def isADTSelector(sym: SSymbol): Boolean = selectors.isDefinedAt(sym)
      def getADTSelector(sym: SSymbol): Identifier = selectors.get(sym).getOrElse {
        throw new MissformedTIPException("unknown ADT selector " + sym, sym.optPos)
      }

      def withADTSelectors(seq: Seq[(SSymbol, Identifier)]): Locals =
        new Locals(funs, adts, selectors ++ seq, vars, tps, symbols)

      def isGeneric(sym: SSymbol): Boolean = tps.isDefinedAt(sym)
      def getGeneric(sym: SSymbol): TypeParameter = tps.get(sym).getOrElse {
        throw new MissformedTIPException("unknown generic type " + sym, sym.optPos)
      }

      def withGeneric(sym: SSymbol, tp: TypeParameter): Locals = withGenerics(Seq(sym -> tp))
      def withGenerics(seq: Seq[(SSymbol, TypeParameter)]): Locals =
        new Locals(funs, adts, selectors, vars, tps ++ seq, symbols)

      def isVariable(sym: SSymbol): Boolean = vars.isDefinedAt(sym)
      def getVariable(sym: SSymbol): Variable = vars.get(sym).getOrElse {
        throw new MissformedTIPException("unknown variable " + sym, sym.optPos)
      }

      def withVariable(sym: SSymbol, v: Variable): Locals = withVariables(Seq(sym -> v))
      def withVariables(seq: Seq[(SSymbol, Variable)]): Locals =
        new Locals(funs, adts, selectors, vars ++ seq, tps, symbols)

      def isFunction(sym: SSymbol): Boolean = funs.isDefinedAt(sym)
      def getFunction(sym: SSymbol): Identifier = funs.get(sym).getOrElse {
        throw new MissformedTIPException("unknown function " + sym, sym.optPos)
      }

      def withFunction(sym: SSymbol, fd: FunDef): Locals = withFunctions(Seq(sym -> fd))
      def withFunctions(fds: Seq[(SSymbol, FunDef)]): Locals =
        new Locals(funs ++ fds.map(p => p._1 -> p._2.id), adts, selectors, vars, tps,
          symbols.withFunctions(fds.map(_._2)))

      def registerADT(adt: ADTDefinition): Locals = registerADTs(Seq(adt))
      def registerADTs(defs: Seq[ADTDefinition]): Locals =
        new Locals(funs, adts, selectors, vars, tps, symbols.withADTs(defs))
    }

    protected val NoLocals: Locals = new Locals(
      Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, NoSymbols)

    protected def getIdentifier(sym: SSymbol): Identifier = {
      // TODO: check keywords!
      FreshIdentifier(sym.name)
    }

    def parseTIPScript: (Symbols, Expr) = {

      var assertions: Seq[Expr] = Seq.empty
      implicit var locals: Locals = NoLocals

      while (peekToken != null) {
        eat(Tokens.OParen)
        val (newAssertions, newLocals) = parseTIPCommand(nextToken)
        assertions ++= newAssertions
        locals = newLocals
        eat(Tokens.CParen)
      }

      val expr: Expr = locals.symbols.andJoin(assertions)
      (locals.symbols, expr)
    }

    protected def parseParTerm(implicit locals: Locals): Expr = getPeekToken.kind match {
      case Tokens.OParen =>
        eat(Tokens.OParen)
        getPeekToken.kind match {
          case Tokens.Par =>
            eat(Tokens.Par)
            val tps = parseMany(parseSymbol _)
            val res = parseTerm
            eat(Tokens.CParen)
            extractExpr(res)(locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos))))

          case _ =>
            extractExpr(parseBefore(Tokens.CParen)(parseTermWithoutParens _))
        }
      case _ =>
        extractExpr(parseTerm)
    }

    protected def parseTIPCommand(token: Tokens.Token)
                                 (implicit locals: Locals): (Option[Expr], Locals) = token match {
      case Tokens.SymbolLit("assert-not") =>
        (Some(Not(parseParTerm)), locals)

      case Tokens.Token(Tokens.Assert) =>
        (Some(parseParTerm), locals)

      case Tokens.Token(Tokens.DefineFun) | Tokens.Token(Tokens.DefineFunRec) =>
        val isRec = token.kind == Tokens.DefineFunRec
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

        val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
        val fdsLocals = if (!isRec) tpsLocals else {
          tpsLocals.withFunction(funDef.name, extractSignature(funDef, tps)(tpsLocals))
        }
        val fd = extractFunction(funDef, tps)(fdsLocals)
        (None, locals.withFunction(funDef.name, fd))

      case Tokens.Token(Tokens.DefineFunsRec) =>
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
          val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
          funDef.name -> extractSignature(funDef, tps)(tpsLocals)
        })

        (None, locals.withFunctions(for ((tps, funDef) <- funDefs) yield {
          val tpsLocals = bodyLocals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
          funDef.name -> extractFunction(funDef, tps)(tpsLocals)
        }))

      case Tokens.Token(Tokens.DeclareDatatypes) =>
        val tps = parseMany(parseSymbol _)
        val datatypes = parseMany(parseDatatypes _)

        var locs = locals.withADTs(datatypes
          .flatMap { case (sym, conss) =>
            val tpeId = getIdentifier(sym)
            val cids = if (conss.size == 1) {
              Seq(conss.head.sym -> tpeId)
            } else {
              conss.map(c => c.sym -> getIdentifier(c.sym))
            }
            (sym -> tpeId) +: cids
          })

        val generics = tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos))
        for ((sym, conss) <- datatypes) {
          val adtLocals = locs.withGenerics(generics)
          val children = for (Constructor(sym, fields) <- conss) yield {
            val id = locs.getADT(sym)
            val vds = fields.map { case (s, sort) =>
              ValDef(getIdentifier(s), extractType(sort)(adtLocals)).setPos(s.optPos)
            }

            (id, vds)
          }

          val allVds: Set[ValDef] = children.flatMap(_._2).toSet
          val allTparams: Set[TypeParameter] = children.flatMap(_._2).toSet.flatMap {
            (vd: ValDef) => locs.symbols.typeParamsOf(vd.tpe): Set[TypeParameter]
          }

          val tparams: Seq[TypeParameterDef] = tps.flatMap { sym =>
            val tp = adtLocals.getGeneric(sym)
            if (allTparams(tp)) Some(TypeParameterDef(tp).setPos(sym.optPos)) else None
          }

          val parent = if (children.size > 1) {
            val id = adtLocals.getADT(sym)
            locs = locs.registerADT(
              new ADTSort(id, tparams, children.map(_._1), Set.empty).setPos(sym.optPos))
            Some(id)
          } else {
            None
          }

          locs = locs.registerADTs((conss zip children).map { case (cons, (cid, vds)) =>
            new ADTConstructor(cid, tparams, parent, vds, Set.empty).setPos(cons.sym.optPos)
          }).withADTSelectors((conss zip children).flatMap { case (Constructor(_, fields), (_, vds)) =>
            (fields zip vds).map(p => p._1._1 -> p._2.id)
          })
        }

        (None, locs)

      case Tokens.Token(Tokens.DeclareConst) =>
        val sym = parseSymbol
        val sort = parseSort
        (None, locals.withVariable(sym,
          Variable(getIdentifier(sym), extractType(sort)).setPos(sym.optPos)))

      case Tokens.Token(Tokens.DeclareSort) =>
        val sym = parseSymbol
        val arity = parseNumeral.value.toInt
        val id = getIdentifier(sym)
        (None, locals.withADT(sym, id).registerADT {
          val tparams = List.range(0, arity).map {
            i => TypeParameterDef(TypeParameter.fresh("A" + i).setPos(sym.optPos)).setPos(sym.optPos)
          }
          val field = ValDef(FreshIdentifier("val"), IntegerType).setPos(sym.optPos)

          new ADTConstructor(id, tparams, None, Seq(field), Set.empty)
        })

      case Tokens.Token(Tokens.CheckSat) =>
        // TODO: what do I do with this??
        (None, locals)

      case token =>
        throw new MissformedTIPException("unknown TIP command " + token, token.optPos)
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
      val tparams = tps.map(sym => TypeParameterDef(locals.getGeneric(sym)).setPos(sym.optPos))

      val params = fd.params.map { case SortedVar(s, sort) =>
        ValDef(getIdentifier(s), extractType(sort)).setPos(s.optPos)
      }

      val returnType = extractType(fd.returnSort)
      val body = Choose(ValDef(FreshIdentifier("res"), returnType), BooleanLiteral(true))

      new FunDef(id, tparams, params, returnType, body, Set.empty).setPos(fd.name.optPos)
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

      new FunDef(sig.id, sig.tparams, sig.params, sig.returnType, fullBody, Set.empty).setPos(fd.name.optPos)
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

      // freshen the type parameters in case we're building a substitution that includes params from `tps`
      val tpSubst: Map[Type, Type] = locals.symbols.typeParamsOf(actual).map(tp => tp -> tp.freshen).toMap
      val tpRSubst = tpSubst.map(_.swap)
      val substActual = locals.symbols.typeOps.replace(tpSubst, actual)

      canBeSupertypeOf(formal, substActual) match {
        case Some(tmap) => tps.map(tpd => tmap.get(tpd.tp).map {
          tpe => locals.symbols.typeOps.replace(tpRSubst, tpe)
        }.getOrElse(tpd.tp))

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

    protected def extractExpr(term: Term)(implicit locals: Locals): Expr = (term match {
      case QualifiedIdentifier(SimpleIdentifier(sym), None) if locals.isVariable(sym) =>
        locals.getVariable(sym)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("assume")), None), Seq(pred, body)) =>
        Assume(extractExpr(pred), extractExpr(body))

      case SMTLet(binding, bindings, term) =>
        var locs = locals
        val mapping = for (VarBinding(name, term) <- (binding +: bindings)) yield {
          val e = extractExpr(term)(locs)
          val tpe = e.getType(locs.symbols)
          val vd = ValDef(getIdentifier(name), tpe).setPos(name.optPos)
          locs = locs.withVariable(name, vd.toVariable)
          vd -> e
        }

        mapping.foldRight(extractExpr(term)(locs)) { case ((vd, e), body) => Let(vd, e, body).setPos(vd.getPos) }

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("@")), None), fun +: args) =>
        Application(extractExpr(fun), args.map(extractExpr))

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("lambda")), None), args :+ body) =>
        val (vds, bindings) = args.map { case QualifiedIdentifier(SimpleIdentifier(s), Some(sort)) =>
          val vd = ValDef(getIdentifier(s), extractType(sort)).setPos(s.optPos)
          (vd, s -> vd.toVariable)
        }.unzip

        Lambda(vds, extractExpr(body)(locals.withVariables(bindings)))

      case SMTForall(sv, svs, term) =>
        val (vds, bindings) = (sv +: svs).map { case SortedVar(s, sort) =>
          val vd = ValDef(getIdentifier(s), extractType(sort)).setPos(s.optPos)
          (vd, s -> vd.toVariable)
        }.unzip

        Forall(vds, extractExpr(term)(locals.withVariables(bindings)))

      case Exists(sv, svs, term) =>
        val (vds, bindings) = (sv +: svs).map { case SortedVar(s, sort) =>
          val vd = ValDef(getIdentifier(s), extractType(sort)).setPos(s.optPos)
          (vd, s -> vd.toVariable)
        }.unzip

        val body = Not(extractExpr(term)(locals.withVariables(bindings))).setPos(term.optPos)
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

      case QualifiedIdentifier(SimpleIdentifier(sym), optSort) if locals.isADT(sym) =>
        val cons = locals.symbols.getADT(locals.getADT(sym)).asInstanceOf[ADTConstructor]
        val tpe = optSort match {
          case Some(sort) =>
            val tps = instantiateTypeParams(
              cons.tparams,
              Seq(cons.typed(locals.symbols).toType),
              Seq(extractType(sort)))
            cons.typed(tps)(locals.symbols).toType
          case _ =>
            assert(cons.tparams.isEmpty)
            cons.typed(locals.symbols).toType
        }
        ADT(tpe, Seq.empty)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args)
      if locals.isADT(sym) =>
        val es = args.map(extractExpr)
        val cons = locals.symbols.getADT(locals.getADT(sym)).asInstanceOf[ADTConstructor]
        val tps = instantiateTypeParams(cons.tparams, cons.fields.map(_.tpe), es.map(_.getType(locals.symbols)))
        val tcons = cons.typed(tps)(locals.symbols)
        ADT(tcons.toType, wrapAsInstanceOf(tcons.fieldsTypes, es))

      case QualifiedIdentifier(SimpleIdentifier(sym), optSort) if locals.isFunction(sym) =>
        val fd = locals.symbols.getFunction(locals.getFunction(sym))
        val tfd = optSort match {
          case Some(sort) =>
            val tpe = extractType(sort)
            val tps = instantiateTypeParams(fd.tparams, Seq(fd.returnType), Seq(tpe))
            fd.typed(tps)(locals.symbols)

          case None =>
            fd.typed(locals.symbols)
        }
        tfd.applied

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

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("distinct")), None), args) =>
        val es = args.map(extractExpr).toArray
        val indexPairs = args.indices.flatMap(i1 => args.indices.map(i2 => (i1, i2))).filter(p => p._1 != p._2)
        locals.symbols.andJoin(
          indexPairs.map(p => Not(Equals(es(p._1), es(p._2)).setPos(term.optPos)).setPos(term.optPos)))

      case Core.Equals(e1, e2) => Equals(extractExpr(e1), extractExpr(e2))
      case Core.And(es @ _*) => And(es.map(extractExpr))
      case Core.Or(es @ _*) => Or(es.map(extractExpr))
      case Core.Implies(e1, e2) => Implies(extractExpr(e1), extractExpr(e2))
      case Core.Not(e) => Not(extractExpr(e))

      case Core.True() => BooleanLiteral(true)
      case Core.False() => BooleanLiteral(false)

      case Strings.Length(s) => StringLength(extractExpr(s))
      case Strings.Concat(e1, e2, es @ _*) =>
        es.foldLeft(StringConcat(extractExpr(e1), extractExpr(e2)).setPos(term.optPos)) {
          (c,e) => StringConcat(c, extractExpr(e)).setPos(term.optPos)
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
          LessThan(ie, IntegerLiteral(BigInt(0)).setPos(term.optPos)).setPos(term.optPos),
          UMinus(ie).setPos(term.optPos),
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
              (Some(IsInstanceOf(scrut, tpe).setPos(sym.optPos)), extractExpr(term))

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
                val selector = ADTSelector(AsInstanceOf(scrut, tpe).setPos(s.optPos), id).setPos(s.optPos)
                Let(vd, selector, e).setPos(s.optPos)
              }

              (Some(IsInstanceOf(scrut, tpe).setPos(sym.optPos)), fullExpr)

            case _ => throw new MissformedTIPException("unexpected match pattern " + pat, pat.optPos)
          }

          case cse => throw new MissformedTIPException("unexpected match case " + cse, cse.optPos)
        }

        val (withCond, withoutCond) = matchCases.partition(_._1.isDefined)
        val (ifs, last) = if (withoutCond.size > 1) {
          throw new MissformedTIPException("unexpected multiple defaults in " + term, term.optPos)
        } else if (withoutCond.size == 1) {
          (withCond.map(p => p._1.get -> p._2), withoutCond.head._2)
        } else {
          val wc = withCond.map(p => p._1.get -> p._2)
          (wc.init, wc.last._2)
        }

        ifs.foldRight(last) { case ((cond, body), elze) => IfExpr(cond, body, elze).setPos(cond.getPos) }

    }).setPos(term.optPos)

    protected def extractType(sort: Sort)(implicit locals: Locals): Type = (sort match {
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

      case _ => throw new MissformedTIPException("unexpected sort: " + sort, sort.id.symbol.optPos)
    }).setPos(sort.id.symbol.optPos)
  }
}

object TIPParser {
  def parse(file: File): (inox.trees.Symbols, inox.trees.Expr) = new TIPParser {
    val trees: inox.trees.type = inox.trees
  }.parse(file)

  def parse(reader: Reader): (inox.trees.Symbols, inox.trees.Expr) = new TIPParser {
    val trees: inox.trees.type = inox.trees
  }.parse(reader)
}
