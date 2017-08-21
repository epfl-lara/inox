/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import utils._

import smtlib.lexer.{Tokens => LT, _}
import smtlib.trees.Commands.{FunDef => SMTFunDef, _}
import smtlib.trees.Terms.{Let => SMTLet, Forall => SMTForall, Identifier => SMTIdentifier, _}
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

  def parseScript: Seq[(InoxProgram, Expr)] = {
    val parser = new TipParser(new TipLexer(positions.reader))
    val script = parser.parseScript

    var assertions: Seq[Expr] = Seq.empty
    implicit var locals: Locals = NoLocals

    (for (cmd <- script.commands) yield cmd match {
      case CheckSat() =>
        val expr: Expr = andJoin(assertions)
        Some((InoxProgram(locals.symbols), expr))

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
    val vars: Map[SSymbol, Expr],
    tps:  Map[SSymbol, TypeParameter],
    val symbols: Symbols) { self =>

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

    object extractor extends {
      val symbols: self.symbols.type = self.symbols
    } with TermExtractor

    def extractTerm(term: Term): Expr = extractor.extractTerm(term)(this)
    def extractSort(sort: Sort): Type = extractor.extractSort(sort)(this)
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
      (Some(locals.extractTerm(term)), locals)

    case AssertPar(tps, term) =>
      val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
      (Some(tpsLocals.extractTerm(term)), locals)

    case DeclareConst(sym, sort) =>
      (None, locals.withVariable(sym,
        Variable.fresh(sym.name, locals.extractSort(sort)).setPos(sym.optPos)))

    case DeclareConstPar(tps, sym, sort) =>
      val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
      (None, locals.withVariable(sym,
        Variable.fresh(sym.name, tpsLocals.extractSort(sort)).setPos(sym.optPos)))

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
            ValDef(FreshIdentifier(s.name), adtLocals.extractSort(sort)).setPos(s.optPos)
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
      val adt = locals.withGenerics(syms zip tps).extractSort(sort) match {
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
          locals.withGenerics(syms zip root.typeArgs)
            .withVariable(s, AsInstanceOf(vd.toVariable, adtType).setPos(s.optPos))
            .extractTerm(pred)
        ).setPos(pred.optPos)
      } else {
        locals.withGenerics(syms zip root.typeArgs)
          .withVariable(s, vd.toVariable)
          .extractTerm(pred)
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
      ValDef(FreshIdentifier(s.name), locals.extractSort(sort)).setPos(s.optPos)
    }

    val returnType = locals.extractSort(fd.returnSort)
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

    val fullBody = bodyLocals.extractTerm(fd.body)

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
    locals.symbols.instantiation_>:(troot, superType) match {
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
    val tpSubst: Map[Type, Type] = typeParamsOf(actual).map(tp => tp -> tp.freshen).toMap
    val tpRSubst = tpSubst.map(_.swap)
    val substActual = typeOps.replace(tpSubst, actual)

    instantiation_>:(formal, substActual) match {
      case Some(tmap) => tps.map(tpd => tmap.get(tpd.tp).map {
        tpe => typeOps.replace(tpRSubst, tpe)
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

  trait TermExtractor extends solvers.smtlib.SMTLIBParser {
    val trees: inox.trees.type = inox.trees

    import trees._
    import symbols._

    protected case class Context(locals: Locals) extends super.AbstractContext {
      val vars = locals.vars
      def withVariable(sym: SSymbol, expr: Expr): Context = Context(locals.withVariable(sym, expr))

      @inline def isADT(sym: SSymbol): Boolean = locals.isADT(sym)
      @inline def lookupADT(sym: SSymbol): Option[Identifier] = locals.lookupADT(sym)
      @inline def getADT(sym: SSymbol): Identifier = locals.getADT(sym)

      @inline def isADTSelector(sym: SSymbol): Boolean = locals.isADTSelector(sym)
      @inline def getADTSelector(sym: SSymbol): Identifier = locals.getADTSelector(sym)

      @inline def isGeneric(sym: SSymbol): Boolean = locals.isGeneric(sym)
      @inline def getGeneric(sym: SSymbol): TypeParameter = locals.getGeneric(sym)

      @inline def isVariable(sym: SSymbol): Boolean = locals.isVariable(sym)
      @inline def getVariable(sym: SSymbol): Expr = locals.getVariable(sym)

      @inline def isFunction(sym: SSymbol): Boolean = locals.isFunction(sym)
      @inline def getFunction(sym: SSymbol): Identifier = locals.getFunction(sym)
    }

    def extractTerm(term: Term)(implicit locals: Locals): Expr = fromSMT(term)(Context(locals))
    def extractSort(sort: Sort)(implicit locals: Locals): Type = fromSMT(sort)(Context(locals))

    override protected def fromSMT(term: Term, otpe: Option[Type] = None)(implicit ctx: Context): Expr = (term match {
      case QualifiedIdentifier(SimpleIdentifier(sym), None) if ctx.isVariable(sym) =>
        ctx.getVariable(sym)

      case QualifiedIdentifier(SimpleIdentifier(sym), Some(sort)) if ctx.isVariable(sym) =>
        val v = ctx.getVariable(sym).asInstanceOf[Variable]
        Variable(v.id, fromSMT(sort), v.flags)

      case SMTAssume(pred, body) =>
        Assume(fromSMT(pred), fromSMT(body))

      case SMTChoose(sym, sort, pred) =>
        val vd = ValDef(FreshIdentifier(sym.name), fromSMT(sort))
        Choose(vd, fromSMT(pred)(ctx.withVariable(sym, vd.toVariable)))

      case SMTLet(binding, bindings, term) =>
        var context = ctx
        val mapping = for (VarBinding(name, term) <- (binding +: bindings)) yield {
          val e = fromSMT(term)(context)
          val vd = ValDef(FreshIdentifier(name.name), e.getType).setPos(name.optPos)
          context = context.withVariable(name, vd.toVariable)
          vd -> e
        }
        mapping.foldRight(fromSMT(term)(context)) { case ((vd, e), body) => Let(vd, e, body).setPos(vd) }

      case SMTApplication(caller, args) =>
        Application(fromSMT(caller), args.map(fromSMT(_)))

      case SMTLambda(svs, term) =>
        val (vds, bindings) = svs.map { case SortedVar(s, sort) =>
          val vd = ValDef(FreshIdentifier(s.name), fromSMT(sort)).setPos(s.optPos)
          (vd, s -> vd.toVariable)
        }.unzip
        otpe match {
          case Some(FunctionType(_, to)) => Lambda(vds, fromSMT(term, to)(ctx.withVariables(bindings)))
          case _ => Lambda(vds, fromSMT(term)(ctx.withVariables(bindings)))
        }

      case QualifiedIdentifier(SimpleIdentifier(sym), optSort) if ctx.isADT(sym) =>
        val cons = symbols.getADT(ctx.getADT(sym)).asInstanceOf[ADTConstructor]
        val tpe = optSort match {
          case Some(sort) =>
            val tps = instantiateTypeParams(
              cons.tparams,
              Seq(cons.typed.toType),
              Seq(fromSMT(sort)))(ctx.locals)
            cons.typed(tps).toType
          case _ =>
            assert(cons.tparams.isEmpty)
            cons.typed.toType
        }
        ADT(tpe, Seq.empty)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args)
      if ctx.isADT(sym) =>
        val es = args.map(fromSMT(_))
        val cons = symbols.getADT(ctx.getADT(sym)).asInstanceOf[ADTConstructor]
        val tps = instantiateTypeParams(cons.tparams, cons.fields.map(_.tpe), es.map(_.getType))(ctx.locals)
        val tcons = cons.typed(tps)
        ADT(tcons.toType, wrapAsInstanceOf(tcons.fieldsTypes, es)(ctx.locals))

      case QualifiedIdentifier(SimpleIdentifier(sym), optSort) if ctx.isFunction(sym) =>
        val fd = symbols.getFunction(ctx.getFunction(sym))
        val tfd = optSort match {
          case Some(sort) =>
            val tpe = fromSMT(sort)
            val tps = instantiateTypeParams(fd.tparams, Seq(fd.returnType), Seq(tpe))(ctx.locals)
            fd.typed(tps)

          case None =>
            fd.typed
        }
        tfd.applied

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), optSort), args)
      if ctx.isFunction(sym) =>
        val es = args.map(fromSMT(_))
        val fd = symbols.getFunction(ctx.getFunction(sym))
        val tps = optSort match {
          case Some(sort) =>
            val tpe = fromSMT(sort)
            instantiateTypeParams(
              fd.tparams,
              fd.params.map(_.tpe) :+ fd.returnType,
              es.map(_.getType) :+ tpe
            )(ctx.locals)

          case None =>
            instantiateTypeParams(fd.tparams, fd.params.map(_.tpe), es.map(_.getType))(ctx.locals)
        }
        val tfd = fd.typed(tps)
        tfd.applied(wrapAsInstanceOf(tfd.params.map(_.tpe), es)(ctx.locals))

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), Seq(term))
      if isInstanceOfSymbol(sym)(ctx.locals).isDefined =>
        val e = fromSMT(term)
        val tpe = typeADTConstructor(isInstanceOfSymbol(sym)(ctx.locals).get, e.getType)(ctx.locals)
        IsInstanceOf(e, tpe)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), Seq(term))
      if ctx.isADTSelector(sym) =>
        val id = ctx.getADTSelector(sym)
        val adt = fromSMT(term)
        adt.getType match {
          case tpe: ADTType => tpe.getADT match {
            case tcons: TypedADTConstructor => ADTSelector(adt, id)
            case tsort: TypedADTSort =>
              val tcons = tsort.constructors.find(_.fields.exists(vd => vd.id == id)).getOrElse {
                throw new MissformedTIPException("Coulnd't find corresponding constructor", sym.optPos)
              }
              ADTSelector(AsInstanceOf(adt, tcons.toType).setPos(term.optPos), id)
          }
        }

      /* String theory extractors */

      case Strings.Length(s) => StringLength(fromSMT(s))
      case Strings.Concat(e1, e2, es @ _*) =>
        es.foldLeft(StringConcat(fromSMT(e1), fromSMT(e2)).setPos(term.optPos)) {
          (c,e) => StringConcat(c, fromSMT(e)).setPos(term.optPos)
        }

      case Strings.Substring(e, start, end) =>
        SubString(fromSMT(e), fromSMT(start), fromSMT(end))

      case Sets.Union(e1, e2) => SetUnion(fromSMT(e1), fromSMT(e2))
      case Sets.Intersection(e1, e2) => SetIntersection(fromSMT(e1), fromSMT(e2))
      case Sets.Setminus(e1, e2) => SetDifference(fromSMT(e1), fromSMT(e2))
      case Sets.Member(e1, e2) => ElementOfSet(fromSMT(e1), fromSMT(e2))
      case Sets.Subset(e1, e2) => SubsetOf(fromSMT(e1), fromSMT(e2))

      case Sets.EmptySet(sort) => FiniteSet(Seq.empty, fromSMT(sort))
      case Sets.Singleton(e) =>
        val elem = fromSMT(e)
        FiniteSet(Seq(elem), bestRealType(elem.getType))

      case Sets.Insert(set, es @ _*) =>
        es.foldLeft(fromSMT(set))((s,e) => SetAdd(s, fromSMT(e)))

      case Bags.Singleton(k, v) =>
        val key = fromSMT(k)
        FiniteBag(Seq(key -> fromSMT(v)), bestRealType(key.getType))

      case Bags.EmptyBag(sort) => FiniteBag(Seq.empty, fromSMT(sort))
      case Bags.Union(e1, e2) => BagUnion(fromSMT(e1), fromSMT(e2))
      case Bags.Intersection(e1, e2) => BagIntersection(fromSMT(e1), fromSMT(e2))
      case Bags.Difference(e1, e2) => BagDifference(fromSMT(e1), fromSMT(e2))
      case Bags.Multiplicity(e1, e2) => MultiplicityInBag(fromSMT(e1), fromSMT(e2))

      case Bags.Insert(bag, es @ _*) =>
        es.foldLeft(fromSMT(bag))((b,e) => BagAdd(b, fromSMT(e)))

      case Match(s, cases) =>
        val scrut = fromSMT(s)
        val matchCases: Seq[(Option[Expr], Expr)] = cases.map(cse => cse.pattern match {
          case Default =>
            (None, fromSMT(cse.rhs))

          case CaseObject(sym) =>
            val id = ctx.getADT(sym)
            val tpe = typeADTConstructor(id, scrut.getType)(ctx.locals)
            (Some(IsInstanceOf(scrut, tpe).setPos(sym.optPos)), fromSMT(cse.rhs))

          case CaseClass(sym, args) =>
            val id = ctx.getADT(sym)
            val tpe = typeADTConstructor(id, scrut.getType)(ctx.locals)

            val tcons = tpe.getADT.toConstructor
            val bindings = (tcons.fields zip args).map { case (vd, sym) => (sym, vd.id, vd.freshen) }

            val expr = fromSMT(cse.rhs)(ctx.withVariables(bindings.map(p => p._1 -> p._3.toVariable)))
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

      case _ => super.fromSMT(term, otpe)
    }).setPos(term.optPos)

    override protected def fromSMT(sort: Sort)(implicit ctx: Context): Type = (sort match {
      case Sets.SetSort(base) => SetType(fromSMT(base))
      case Bags.BagSort(base) => BagType(fromSMT(base))
      case Sort(SimpleIdentifier(SSymbol("=>")), params :+ res) => FunctionType(params.map(fromSMT), fromSMT(res))
      case Sort(SimpleIdentifier(sym), Seq()) if ctx.isGeneric(sym) => ctx.getGeneric(sym)
      case Sort(SimpleIdentifier(sym), tps) if ctx.isADT(sym) => ADTType(ctx.getADT(sym), tps.map(fromSMT))
      case _ => super.fromSMT(sort)
    }).setPos(sort.id.symbol.optPos)
  }
}
