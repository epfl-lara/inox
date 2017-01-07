/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import utils._

import smtlib.lexer.{Tokens => LT, _}
import smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import smtlib.parser.Terms.{Let => SMTLet, Forall => SMTForall, Identifier => SMTIdentifier, _}
import smtlib.theories._
import smtlib.theories.experimental._
import smtlib.extensions.tip.Terms.{Lambda => SMTLambda, Application => SMTApplication, _}
import smtlib.extensions.tip.Commands._

import Terms.{Assume => SMTAssume, Choose => SMTChoose}
import Commands._

import scala.collection.BitSet
import java.io.{Reader, File, BufferedReader, FileReader}

import scala.language.implicitConversions

class MissformedTIPException(reason: String, pos: Position)
  extends Exception("Missfomed TIP source @" + pos + ":\n" + reason)

class Parser(file: File) {
  import inox.trees._

  protected val positions = new PositionProvider(new BufferedReader(new FileReader(file)), Some(file))

  protected implicit def smtlibPositionToPosition(pos: Option[_root_.smtlib.common.Position]): Position = {
    pos.map(p => positions.get(p.line, p.col)).getOrElse(NoPosition)
  }

  def parseScript: Seq[(Symbols, Expr)] = {
    val parser = new TipParser(new TipLexer(positions.reader))
    val script = parser.parseScript

    var assertions: Seq[Expr] = Seq.empty
    implicit var locals: Locals = NoLocals

    (for (cmd <- script.commands) yield cmd match {
      case CheckSat() =>
        val expr: Expr = andJoin(assertions)
        Some((locals.symbols, expr))

      case _ =>
        val (newAssertions, newLocals) = extractCommand(cmd)
        assertions ++= newAssertions
        locals = newLocals
        None
    }).flatten
  }

  protected class Locals (
    funs: Map[SSymbol, Identifier],
    adts: Map[SSymbol, Identifier],
    selectors: Map[SSymbol, Identifier],
    vars: Map[SSymbol, Expr],
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
    def getVariable(sym: SSymbol): Expr = vars.get(sym).getOrElse {
      throw new MissformedTIPException("unknown variable " + sym, sym.optPos)
    }

    def withVariable(sym: SSymbol, v: Expr): Locals = withVariables(Seq(sym -> v))
    def withVariables(seq: Seq[(SSymbol, Expr)]): Locals =
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

    def withSymbols(symbols: Symbols) = new Locals(funs, adts, selectors, vars, tps, symbols)
  }

  protected val NoLocals: Locals = new Locals(
    Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, NoSymbols)

  protected object DatatypeInvariantExtractor {
    def unapply(cmd: Command): Option[(Seq[SSymbol], SSymbol, Sort, Term)] = cmd match {
      case DatatypeInvariantPar(syms, s, sort, pred) => Some((syms, s, sort, pred))
      case DatatypeInvariant(s, sort, pred) => Some((Seq.empty, s, sort, pred))
      case _ => None
    }
  }

  protected def extractCommand(cmd: Command)
                              (implicit locals: Locals): (Option[Expr], Locals) = cmd match {
    case Assert(term) =>
      (Some(extractTerm(term)), locals)

    case AssertPar(tps, term) =>
      val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
      (Some(extractTerm(term)(tpsLocals)), locals)

    case DeclareConst(sym, sort) =>
      (None, locals.withVariable(sym,
        Variable.fresh(sym.name, extractSort(sort)).setPos(sym.optPos)))

    case DeclareConstPar(tps, sym, sort) =>
      val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
      (None, locals.withVariable(sym,
        Variable.fresh(sym.name, extractSort(sort)(tpsLocals)).setPos(sym.optPos)))

    case DeclareFun(name, sorts, returnSort) =>
      (None, locals.withFunction(name, extractSignature(FunDec(name, sorts.map {
        sort => SortedVar(SSymbol(FreshIdentifier("x").uniqueName).setPos(sort), sort).setPos(sort)
      }, returnSort), Seq.empty)))

    case DeclareFunPar(tps, name, sorts, returnSort) =>
      val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
      (None, locals.withFunction(name, extractSignature(FunDec(name, sorts.map {
        sort => SortedVar(SSymbol(FreshIdentifier("x").uniqueName).setPos(sort), sort).setPos(sort)
      }, returnSort), tps)))

    case DefineFun(funDef) =>
      val fd = extractFunction(funDef, Seq.empty)
      (None, locals.withFunction(funDef.name, fd))

    case DefineFunPar(tps, funDef) =>
      val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
      val fd = extractFunction(funDef, tps)(tpsLocals)
      (None, locals.withFunction(funDef.name, fd))

    case DefineFunRec(funDef) =>
      val fdsLocals = locals.withFunction(funDef.name, extractSignature(funDef, Seq.empty))
      val fd = extractFunction(funDef, Seq.empty)(fdsLocals)
      (None, locals.withFunction(funDef.name, fd))

    case DefineFunRecPar(tps, funDef) =>
      val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
      val fdsLocals = tpsLocals.withFunction(funDef.name, extractSignature(funDef, tps)(tpsLocals))
      val fd = extractFunction(funDef, tps)(fdsLocals)
      (None, locals.withFunction(funDef.name, fd))

    case DefineFunsRec(funDecs, bodies) =>
      val funDefs = for ((funDec, body) <- funDecs zip bodies) yield {
        SMTFunDef(funDec.name, funDec.params, funDec.returnSort, body)
      }
      val bodyLocals = locals.withFunctions(for (funDef <- funDefs) yield {
        funDef.name -> extractSignature(funDef, Seq.empty)
      })
      (None, locals.withFunctions(for (funDef <- funDefs) yield {
        funDef.name -> extractFunction(funDef, Seq.empty)(bodyLocals)
      }))

    case DefineFunsRecPar(funDecs, bodies) =>
      val funDefs = for ((funDec, body) <- funDecs zip bodies) yield (funDec match {
        case Left(funDec) => (funDec.tps, SMTFunDef(funDec.name, funDec.params, funDec.returnSort, body))
        case Right(funDec) => (Seq.empty[SSymbol], SMTFunDef(funDec.name, funDec.params, funDec.returnSort, body))
      })
      val bodyLocals = locals.withFunctions(for ((tps, funDef) <- funDefs) yield {
        val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
        funDef.name -> extractSignature(funDef, tps)(tpsLocals)
      })
      (None, locals.withFunctions(for ((tps, funDef) <- funDefs) yield {
        val tpsLocals = bodyLocals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
        funDef.name -> extractFunction(funDef, tps)(tpsLocals)
      }))

    case DeclareDatatypesPar(tps, datatypes) =>
      var locs = locals.withADTs(datatypes
        .flatMap { case (sym, conss) =>
          val tpeId = FreshIdentifier(sym.name)
          val cids = if (conss.size == 1) {
            Seq(conss.head.sym -> tpeId)
          } else {
            conss.map(c => c.sym -> FreshIdentifier(c.sym.name))
          }
          (sym -> tpeId) +: cids
        })

      val generics = tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos))
      for ((sym, conss) <- datatypes) {
        val adtLocals = locs.withGenerics(generics)
        val children = for (Constructor(sym, fields) <- conss) yield {
          val id = locs.getADT(sym)
          val vds = fields.map { case (s, sort) =>
            ValDef(FreshIdentifier(s.name), extractSort(sort)(adtLocals)).setPos(s.optPos)
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

    case DeclareSort(sym, arity) =>
      val id = FreshIdentifier(sym.name)
      (None, locals.withADT(sym, id).registerADT {
        val tparams = List.range(0, arity).map {
          i => TypeParameterDef(TypeParameter.fresh("A" + i).setPos(sym.optPos)).setPos(sym.optPos)
        }
        val field = ValDef(FreshIdentifier("val"), IntegerType).setPos(sym.optPos)

        new ADTConstructor(id, tparams, None, Seq(field), Set.empty).setPos(sym.optPos)
      })

    case DatatypeInvariantExtractor(syms, s, sort, pred) =>
      val tps = syms.map(s => TypeParameter.fresh(s.name).setPos(s.optPos))
      val adt = extractSort(sort)(locals.withGenerics(syms zip tps)) match {
        case adt @ ADTType(id, typeArgs) if tps == typeArgs => adt.getADT(locals.symbols).definition
        case _ => throw new MissformedTIPException(s"Unexpected type parameters $syms", sort.optPos)
      }

      val root = adt.root(locals.symbols)
      val rootType = root.typed(locals.symbols).toType
      val vd = ValDef(FreshIdentifier(s.name), rootType).setPos(s.optPos)

      val body = if (root != adt) {
        val adtType = adt.typed(root.typeArgs)(locals.symbols).toType
        Implies(
          IsInstanceOf(vd.toVariable, adtType).setPos(pred.optPos),
          extractTerm(pred)(
            locals.withGenerics(syms zip root.typeArgs)
              .withVariable(s, AsInstanceOf(vd.toVariable, adtType).setPos(s.optPos))
          )
        ).setPos(pred.optPos)
      } else {
        extractTerm(pred)(locals.withGenerics(syms zip root.typeArgs).withVariable(s, vd.toVariable))
      }

      val (optAdt, fd) = root.invariant(locals.symbols) match {
        case Some(fd) =>
          val Seq(v) = fd.params
          val fullBody = and(
            fd.fullBody,
            exprOps.replaceFromSymbols(Map(v.toVariable -> vd.toVariable), body).setPos(body)
          ).setPos(body)
          (None, fd.copy(fullBody = fullBody))

        case None =>
          val id = FreshIdentifier("inv$" + root.id.name)
          val newAdt = root match {
            case sort: ADTSort => sort.copy(flags = sort.flags + HasADTInvariant(id))
            case cons: ADTConstructor => cons.copy(flags = cons.flags + HasADTInvariant(id))
          }
          val fd = new FunDef(id, root.tparams, Seq(vd), BooleanType, body, Set.empty).setPos(s.optPos)
          (Some(newAdt), fd)
      }

      (None, locals.withSymbols(
        locals.symbols.withFunctions(Seq(fd)).withADTs(optAdt.toSeq)))

    case _ =>
      throw new MissformedTIPException("unknown TIP command " + cmd, cmd.optPos)
  }

  private def extractSignature(fd: FunDec, tps: Seq[SSymbol])(implicit locals: Locals): FunDef = {
    assert(!locals.isFunction(fd.name))
    val id = FreshIdentifier(fd.name.name)
    val tparams = tps.map(sym => TypeParameterDef(locals.getGeneric(sym)).setPos(sym.optPos))

    val params = fd.params.map { case SortedVar(s, sort) =>
      ValDef(FreshIdentifier(s.name), extractSort(sort)).setPos(s.optPos)
    }

    val returnType = extractSort(fd.returnSort)
    val body = Choose(ValDef(FreshIdentifier("res"), returnType), BooleanLiteral(true))

    new FunDef(id, tparams, params, returnType, body, Set.empty).setPos(fd.name.optPos)
  }

  private def extractSignature(fd: SMTFunDef, tps: Seq[SSymbol])(implicit locals: Locals): FunDef = {
    extractSignature(FunDec(fd.name, fd.params, fd.returnSort), tps)
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

    val fullBody = extractTerm(fd.body)(bodyLocals)

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

  protected def extractTerm(term: Term)(implicit locals: Locals): Expr = (term match {
    case QualifiedIdentifier(SimpleIdentifier(sym), None) if locals.isVariable(sym) =>
      locals.getVariable(sym)

    case QualifiedIdentifier(SimpleIdentifier(sym), Some(sort)) if locals.isVariable(sym) =>
      val v = locals.getVariable(sym).asInstanceOf[Variable]
      Variable(v.id, extractSort(sort), v.flags)

    case SMTAssume(pred, body) =>
      Assume(extractTerm(pred), extractTerm(body))

    case SMTChoose(sym, sort, pred) =>
      val vd = ValDef(FreshIdentifier(sym.name), extractSort(sort))
      Choose(vd, extractTerm(pred)(locals.withVariable(sym, vd.toVariable)))

    case SMTLet(binding, bindings, term) =>
      var locs = locals
      val mapping = for (VarBinding(name, term) <- (binding +: bindings)) yield {
        val e = extractTerm(term)(locs)
        val tpe = e.getType(locs.symbols)
        val vd = ValDef(FreshIdentifier(name.name), tpe).setPos(name.optPos)
        locs = locs.withVariable(name, vd.toVariable)
        vd -> e
      }
      mapping.foldRight(extractTerm(term)(locs)) { case ((vd, e), body) => Let(vd, e, body).setPos(vd.getPos) }

    case SMTApplication(caller, args) =>
      Application(extractTerm(caller), args.map(extractTerm))

    case SMTLambda(svs, term) =>
      val (vds, bindings) = svs.map { case SortedVar(s, sort) =>
        val vd = ValDef(FreshIdentifier(s.name), extractSort(sort)).setPos(s.optPos)
        (vd, s -> vd.toVariable)
      }.unzip
      Lambda(vds, extractTerm(term)(locals.withVariables(bindings)))

    case SMTForall(sv, svs, term) =>
      val (vds, bindings) = (sv +: svs).map { case SortedVar(s, sort) =>
        val vd = ValDef(FreshIdentifier(s.name), extractSort(sort)).setPos(s.optPos)
        (vd, s -> vd.toVariable)
      }.unzip
      Forall(vds, extractTerm(term)(locals.withVariables(bindings)))

    case Exists(sv, svs, term) =>
      val (vds, bindings) = (sv +: svs).map { case SortedVar(s, sort) =>
        val vd = ValDef(FreshIdentifier(s.name), extractSort(sort)).setPos(s.optPos)
        (vd, s -> vd.toVariable)
      }.unzip
      val body = Not(extractTerm(term)(locals.withVariables(bindings))).setPos(term.optPos)
      Forall(vds, body)

    case Core.ITE(cond, thenn, elze) =>
      IfExpr(extractTerm(cond), extractTerm(thenn), extractTerm(elze))

    case SNumeral(n) =>
      IntegerLiteral(n)

    case FixedSizeBitVectors.BitVectorLit(bs) =>
      BVLiteral(BitSet.empty ++ bs.reverse.zipWithIndex.collect { case (true, i) => i + 1 }, bs.size)

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
            Seq(extractSort(sort)))
          cons.typed(tps)(locals.symbols).toType
        case _ =>
          assert(cons.tparams.isEmpty)
          cons.typed(locals.symbols).toType
      }
      ADT(tpe, Seq.empty)

    case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args)
    if locals.isADT(sym) =>
      val es = args.map(extractTerm)
      val cons = locals.symbols.getADT(locals.getADT(sym)).asInstanceOf[ADTConstructor]
      val tps = instantiateTypeParams(cons.tparams, cons.fields.map(_.tpe), es.map(_.getType(locals.symbols)))
      val tcons = cons.typed(tps)(locals.symbols)
      ADT(tcons.toType, wrapAsInstanceOf(tcons.fieldsTypes, es))

    case QualifiedIdentifier(SimpleIdentifier(sym), optSort) if locals.isFunction(sym) =>
      val fd = locals.symbols.getFunction(locals.getFunction(sym))
      val tfd = optSort match {
        case Some(sort) =>
          val tpe = extractSort(sort)
          val tps = instantiateTypeParams(fd.tparams, Seq(fd.returnType), Seq(tpe))
          fd.typed(tps)(locals.symbols)

        case None =>
          fd.typed(locals.symbols)
      }
      tfd.applied

    case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args)
    if locals.isFunction(sym) =>
      val es = args.map(extractTerm)
      val fd = locals.symbols.getFunction(locals.getFunction(sym))
      val tps = instantiateTypeParams(fd.tparams, fd.params.map(_.tpe), es.map(_.getType(locals.symbols)))
      val tfd = fd.typed(tps)(locals.symbols)
      tfd.applied(wrapAsInstanceOf(tfd.params.map(_.tpe), es))

    case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), Seq(term))
    if isInstanceOfSymbol(sym).isDefined =>
      val e = extractTerm(term)
      val tpe = typeADTConstructor(isInstanceOfSymbol(sym).get, e.getType(locals.symbols))
      IsInstanceOf(e, tpe)

    case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), Seq(term))
    if locals.isADTSelector(sym) =>
      val id = locals.getADTSelector(sym)
      val adt = extractTerm(term)
      adt.getType(locals.symbols) match {
        case tpe: ADTType => tpe.getADT(locals.symbols) match {
          case tcons: TypedADTConstructor => ADTSelector(adt, id)
          case tsort: TypedADTSort =>
            val tcons = tsort.constructors.find(_.fields.exists(vd => vd.id == id)).getOrElse {
              throw new MissformedTIPException("Coulnd't find corresponding constructor", sym.optPos)
            }
            ADTSelector(AsInstanceOf(adt, tcons.toType).setPos(term.optPos), id)
        }
      }

    case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("distinct")), None), args) =>
      val es = args.map(extractTerm).toArray
      val indexPairs = args.indices.flatMap(i1 => args.indices.map(i2 => (i1, i2))).filter(p => p._1 != p._2)
      andJoin(indexPairs.map(p => Not(Equals(es(p._1), es(p._2)).setPos(term.optPos)).setPos(term.optPos)))

    case Core.Equals(e1, e2) => Equals(extractTerm(e1), extractTerm(e2))
    case Core.And(es @ _*) => And(es.map(extractTerm))
    case Core.Or(es @ _*) => Or(es.map(extractTerm))
    case Core.Implies(e1, e2) => Implies(extractTerm(e1), extractTerm(e2))
    case Core.Not(e) => Not(extractTerm(e))

    case Core.True() => BooleanLiteral(true)
    case Core.False() => BooleanLiteral(false)

    case Strings.Length(s) => StringLength(extractTerm(s))
    case Strings.Concat(e1, e2, es @ _*) =>
      es.foldLeft(StringConcat(extractTerm(e1), extractTerm(e2)).setPos(term.optPos)) {
        (c,e) => StringConcat(c, extractTerm(e)).setPos(term.optPos)
      }

    case Strings.Substring(e, start, end) =>
      SubString(extractTerm(e), extractTerm(start), extractTerm(end))

    /* Ints extractors cover the Reals operations as well */

    case Ints.Neg(e) => UMinus(extractTerm(e))
    case Ints.Add(e1, e2) => Plus(extractTerm(e1), extractTerm(e2))
    case Ints.Sub(e1, e2) => Minus(extractTerm(e1), extractTerm(e2))
    case Ints.Mul(e1, e2) => Times(extractTerm(e1), extractTerm(e2))
    case Ints.Div(e1, e2) => Division(extractTerm(e1), extractTerm(e2))
    case Ints.Mod(e1, e2) => Modulo(extractTerm(e1), extractTerm(e2))
    case Ints.Abs(e) =>
      val ie = extractTerm(e)
      IfExpr(
        LessThan(ie, IntegerLiteral(BigInt(0)).setPos(term.optPos)).setPos(term.optPos),
        UMinus(ie).setPos(term.optPos),
        ie
      )

    case Ints.LessThan(e1, e2) => LessThan(extractTerm(e1), extractTerm(e2))
    case Ints.LessEquals(e1, e2) => LessEquals(extractTerm(e1), extractTerm(e2))
    case Ints.GreaterThan(e1, e2) => GreaterThan(extractTerm(e1), extractTerm(e2))
    case Ints.GreaterEquals(e1, e2) => GreaterEquals(extractTerm(e1), extractTerm(e2))

    case FixedSizeBitVectors.Not(e) => BVNot(extractTerm(e))
    case FixedSizeBitVectors.Neg(e) => UMinus(extractTerm(e))
    case FixedSizeBitVectors.And(e1, e2) => BVAnd(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.Or(e1, e2) => BVOr(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.XOr(e1, e2) => BVXor(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.Add(e1, e2) => Plus(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.Sub(e1, e2) => Minus(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.Mul(e1, e2) => Times(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.SDiv(e1, e2) => Division(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.SRem(e1, e2) => Remainder(extractTerm(e1), extractTerm(e2))

    case FixedSizeBitVectors.SLessThan(e1, e2) => LessThan(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.SLessEquals(e1, e2) => LessEquals(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.SGreaterThan(e1, e2) => GreaterThan(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.SGreaterEquals(e1, e2) => GreaterEquals(extractTerm(e1), extractTerm(e2))

    case FixedSizeBitVectors.ShiftLeft(e1, e2) => BVShiftLeft(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.AShiftRight(e1, e2) => BVAShiftRight(extractTerm(e1), extractTerm(e2))
    case FixedSizeBitVectors.LShiftRight(e1, e2) => BVLShiftRight(extractTerm(e1), extractTerm(e2))

    case ArraysEx.Select(e1, e2) => MapApply(extractTerm(e1), extractTerm(e2))
    case ArraysEx.Store(e1, e2, e3) => MapUpdated(extractTerm(e1), extractTerm(e2), extractTerm(e3))
    case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("const")), Some(sort)), Seq(dflt)) =>
      val d = extractTerm(dflt)
      FiniteMap(Seq.empty, d, extractSort(sort), locals.symbols.bestRealType(d.getType(locals.symbols)))

    case Sets.Union(e1, e2) => SetUnion(extractTerm(e1), extractTerm(e2))
    case Sets.Intersection(e1, e2) => SetIntersection(extractTerm(e1), extractTerm(e2))
    case Sets.Setminus(e1, e2) => SetDifference(extractTerm(e1), extractTerm(e2))
    case Sets.Member(e1, e2) => ElementOfSet(extractTerm(e1), extractTerm(e2))
    case Sets.Subset(e1, e2) => SubsetOf(extractTerm(e1), extractTerm(e2))

    case Sets.EmptySet(sort) => FiniteSet(Seq.empty, extractSort(sort))
    case Sets.Singleton(e) =>
      val elem = extractTerm(e)
      FiniteSet(Seq(elem), locals.symbols.bestRealType(elem.getType(locals.symbols)))

    case Sets.Insert(set, es @ _*) =>
      es.foldLeft(extractTerm(set))((s,e) => SetAdd(s, extractTerm(e)))

    case Bags.Singleton(k, v) =>
      val key = extractTerm(k)
      FiniteBag(Seq(key -> extractTerm(v)), locals.symbols.bestRealType(key.getType(locals.symbols)))

    case Bags.EmptyBag(sort) => FiniteBag(Seq.empty, extractSort(sort))
    case Bags.Union(e1, e2) => BagUnion(extractTerm(e1), extractTerm(e2))
    case Bags.Intersection(e1, e2) => BagIntersection(extractTerm(e1), extractTerm(e2))
    case Bags.Difference(e1, e2) => BagDifference(extractTerm(e1), extractTerm(e2))
    case Bags.Multiplicity(e1, e2) => MultiplicityInBag(extractTerm(e1), extractTerm(e2))

    case Bags.Insert(bag, es @ _*) =>
      es.foldLeft(extractTerm(bag))((b,e) => BagAdd(b, extractTerm(e)))

    case Match(s, cases) =>
      val scrut = extractTerm(s)
      val matchCases: Seq[(Option[Expr], Expr)] = cases.map(cse => cse.pattern match {
        case Default =>
          (None, extractTerm(cse.rhs))

        case CaseObject(sym) =>
          val id = locals.getADT(sym)
          val tpe = typeADTConstructor(id, scrut.getType(locals.symbols))
          (Some(IsInstanceOf(scrut, tpe).setPos(sym.optPos)), extractTerm(cse.rhs))

        case CaseClass(sym, args) =>
          val id = locals.getADT(sym)
          val tpe = typeADTConstructor(id, scrut.getType(locals.symbols))

          val tcons = tpe.getADT(locals.symbols).toConstructor
          val bindings = (tcons.fields zip args).map { case (vd, sym) => (sym, vd.id, vd.freshen) }

          val expr = extractTerm(cse.rhs)(locals.withVariables(bindings.map(p => p._1 -> p._3.toVariable)))
          val fullExpr = bindings.foldRight(expr) { case ((s, id, vd), e) =>
            val selector = ADTSelector(AsInstanceOf(scrut, tpe).setPos(s.optPos), id).setPos(s.optPos)
            Let(vd, selector, e).setPos(s.optPos)
          }
          (Some(IsInstanceOf(scrut, tpe).setPos(sym.optPos)), fullExpr)
      })

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

  protected def extractSort(sort: Sort)(implicit locals: Locals): Type = (sort match {
    case Sort(SMTIdentifier(SSymbol("bitvector" | "BitVec"), Seq(SNumeral(n))), Seq()) => BVType(n.toInt)
    case Sort(SimpleIdentifier(SSymbol("Bool")), Seq()) => BooleanType
    case Sort(SimpleIdentifier(SSymbol("Int")), Seq()) => IntegerType

    case Sort(SimpleIdentifier(SSymbol("Array")), Seq(from, to)) =>
      MapType(extractSort(from), extractSort(to))

    case Sets.SetSort(base) =>
      SetType(extractSort(base))

    case Bags.BagSort(base) =>
      BagType(extractSort(base))

    case Sort(SimpleIdentifier(SSymbol("=>")), params :+ res) =>
      FunctionType(params.map(extractSort), extractSort(res))

    case Sort(SimpleIdentifier(sym), Seq()) if locals.isGeneric(sym) =>
      locals.getGeneric(sym)

    case Sort(SimpleIdentifier(sym), tps) if locals.isADT(sym) =>
      ADTType(locals.getADT(sym), tps.map(extractSort))

    case _ => throw new MissformedTIPException("unexpected sort: " + sort, sort.id.symbol.optPos)
  }).setPos(sort.id.symbol.optPos)
}
