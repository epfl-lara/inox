/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package smtlib3

import smtlib.trees.Commands.{FunDef => SMTFunDef, _}
import smtlib.trees.Terms.{Let => SMTLet, Forall => SMTForall, Identifier => SMTIdentifier, _}
import smtlib.extensions.tip.Terms.{Lambda => SMTLambda, Application => SMTApplication, Match, Case, Default, CaseObject}

import inox.tip.{MissformedTIPException, TipParser}

import java.io.{Reader, File, FileReader}

import scala.language.implicitConversions

/** A type defined by `define-type` (or `define-sort`), expanded where it is used.
  *
  * @param params the type parameters (`Left`) and value parameters (`Right`) of the definition
  * @param body   the defined type, which refers to the parameters
  */
private[smtlib3] case class TypeDefinition(params: Seq[Either[inox.trees.TypeParameter, inox.trees.Variable]],
                                           body: inox.trees.Type)

/** Parses SMT-LIB 3 scripts (see https://smt-lib.org/version3.shtml) into Inox programs.
  *
  * The parser extends the TIP parser of [[inox.tip.Parser]], so it also accepts TIP inputs and the
  * Inox extensions to it (e.g. `datatype-invariant`, `assume` and `choose`). On top of these, it
  * supports the following SMT-LIB 3 features:
  *
  *  - Function types `(-> A B C)` (also spelled `→`), and dependent function types whose parameters
  *    bind variables with `(! A :var x)`, which become Inox `PiType`s.
  *  - Predicate subtypes `(! A :var x :restrict p)`, which become Inox `RefinementType`s.
  *  - Rank-1 polymorphism through global type variables (`declare-type-var`): the declarations
  *    and definitions that mention type variables become polymorphic functions.
  *  - `declare-type`, and `define-type` with type and value parameters.
  *  - `define-const` and `define-const-rec`.
  *  - Curried and partial applications of functions, and the higher-order forms of the binders,
  *    e.g. `(forall p)` or `(choose (lambda ((x Int)) (> x 0)))`.
  *  - SMT-LIB 2.6+ `declare-datatype(s)` and `match` syntax, and testers `(_ is c)`.
  *  - `(BitVec n)` for constant widths `n`.
  *
  * Modules, implicit parameters (`:implicit`) and value-dependent widths and datatypes aren't supported.
  * Constants of function type are free variables of the corresponding (dependent) function type, so
  * that they appear in models, unless their type mentions type variables. In that case, they are
  * declared as polymorphic functions, which hold their codomain refinements in their domain only.
  */
class Parser(reader: Reader, file: Option[File]) extends tip.Parser(reader, file) {
  import inox.trees.{given, _}
  import Terms._
  import Commands._

  override protected def newParser(reader: Reader): TipParser =
    new SMTLIB3Parser(new SMTLIB3Lexer(new ArrowReader(reader)))

  override protected def newExtractor(symbols: Symbols): TermExtractor = new SMTLIB3Extractor(symbols)

  /** The global type variables, in declaration order. */
  private var typeVars: Seq[TypeParameter] = Seq.empty

  private var typeDefs: Map[SSymbol, TypeDefinition] = Map.empty

  private def error(reason: String, pos: Option[smtlib.common.Position]): Nothing =
    throw new MissformedTIPException(reason, pos)

  private def isArrow(sym: SSymbol): Boolean = sym.name == "->"

  /** The global type variables that `types` mention, which become the type parameters of definitions. */
  private def typeVarsOf(types: Seq[Type]): Seq[TypeParameter] = {
    val tps = types.flatMap(typeOps.typeParamsOf(_)).toSet
    typeVars.filter(tps)
  }

  override protected def extractSignature(fd: FunDec, tps: Seq[SSymbol])(using locals: Locals): FunDef = {
    assert(!locals.isFunction(fd.name))
    val id = FreshIdentifier(fd.name.name)

    // The parameter types and the return type may refer to the previous parameters
    var bodyLocals = locals
    val params = fd.params.map { case SortedVar(s, sort) =>
      val vd = ValDef.fresh(s.name, bodyLocals.extractSort(sort)).setPos(s.optPos)
      bodyLocals = bodyLocals.withVariable(s, vd.toVariable)
      vd
    }
    val returnType = bodyLocals.extractSort(fd.returnSort)

    val explicitTps = tps.map(locals.getGeneric)
    val implicitTps = typeVarsOf(params.map(_.tpe) :+ returnType).filterNot(explicitTps.contains)
    val tparams = (explicitTps ++ implicitTps).map(tp => TypeParameterDef(tp).setPos(tp))

    val body = Choose(ValDef.fresh("res", returnType), BooleanLiteral(true))
    new FunDef(id, tparams, params, returnType, body, Seq.empty).setPos(fd.name.optPos)
  }

  /** Declares a polymorphic constant of type `tpe` as a function without body.
    *
    * The codomain refinement of a dependent function type only holds in its domain, so it is
    * guarded by the domain refinements in the declared return type. */
  private def declarePolymorphic(sym: SSymbol, tpe: Type, tps: Seq[TypeParameter]): FunDef = {
    val (params, to) = tpe match {
      case FunctionType(from, to) => (from.map(ValDef.fresh("x", _)), to)
      case PiType(params, to) => (params, to)
      case _ => (Seq.empty, tpe)
    }

    val domain = andJoin(params.map(vd => vd.tpe match {
      case RefinementType(rvd, pred) => exprOps.replaceFromSymbols(Map(rvd -> vd.toVariable), pred)
      case _ => BooleanLiteral(true)
    }))

    val returnType = (to, domain) match {
      case (_, BooleanLiteral(true)) => to
      case (RefinementType(rvd, pred), _) => RefinementType(rvd, implies(domain, pred))
      case _ => to
    }

    val body = Choose(ValDef.fresh("res", returnType), BooleanLiteral(true))
    new FunDef(FreshIdentifier(sym.name), tps.map(TypeParameterDef(_)), params, returnType, body, Seq.empty)
      .setPos(sym.optPos)
  }

  override protected def extractCommand(cmd: Command)(using locals: Locals): (Option[Expr], Locals) = cmd match {
    case _: SetLogic | _: SetInfo | _: SetOption | _: GetModel | _: GetInfo | _: GetValue |
         _: GetAssertions | _: GetAssignment | _: GetUnsatCore | _: GetProof | _: Echo | _: Exit =>
      (None, locals)

    case DeclareTypeVar(sym) =>
      val tp = TypeParameter.fresh(sym.name).setPos(sym.optPos)
      typeVars :+= tp
      (None, locals.withGeneric(sym, tp))

    case DeclareType(sym, kinds) =>
      for (kind <- kinds) kind match {
        case Sort(SimpleIdentifier(SSymbol("Type")), Seq()) =>
        case _ => error(s"unsupported kind $kind of $sym (only types of kind Type can be declared)", kind.optPos)
      }
      super.extractCommand(DeclareSort(sym, kinds.size).setPos(cmd))

    case DefineSort(sym, params, sort) =>
      extractCommand(DefineType(sym, params.map(TypeParam(_)), sort).setPos(cmd))

    case DefineType(sym, params, body) =>
      var bodyLocals = locals
      val ps = params.map {
        case TypeParam(s) =>
          val tp = TypeParameter.fresh(s.name).setPos(s.optPos)
          bodyLocals = bodyLocals.withGeneric(s, tp)
          Left(tp)
        case ValueParam(VarAnnotation(base, Some(n), _, _, _)) =>
          // The restrictions of value parameters only document the definition, as in SMT-LIB 3
          val v = Variable.fresh(n.name, bodyLocals.extractSort(TermSort(base))).setPos(n.optPos)
          bodyLocals = bodyLocals.withVariable(n, v)
          Right(v)
        case p => error(s"unexpected type parameter $p", sym.optPos)
      }
      typeDefs += sym -> TypeDefinition(ps, bodyLocals.extractSort(body))
      (None, locals)

    case DeclareConst(sym, sort) =>
      val tpe = locals.extractSort(sort)
      typeVarsOf(Seq(tpe)) match {
        case Seq() =>
          (None, locals.withVariable(sym, Variable.fresh(sym.name, tpe).setPos(sym.optPos)))
        case tps =>
          (None, locals.withFunction(sym, declarePolymorphic(sym, tpe, tps)))
      }

    case DefineConst(sym, sort, body, isRec) =>
      val funDef = (TermSort.toTerm(sort), body) match {
        case (FunctionApplication(QualifiedIdentifier(SimpleIdentifier(arrow), None), types), SMTLambda(params, lbody))
          if isArrow(arrow) && params.size < types.size =>
          val rest = types.drop(params.size)
          val returnSort = if (rest.size == 1) TermSort(rest.head) else {
            TermSort(FunctionApplication(QualifiedIdentifier(SimpleIdentifier(arrow)), rest))
          }
          SMTFunDef(sym, params, returnSort, lbody)
        case _ =>
          SMTFunDef(sym, Seq.empty, sort, body)
      }
      super.extractCommand((if (isRec) DefineFunRec(funDef) else DefineFun(funDef)).setPos(cmd))

    case DeclareDatatypesWithPars(datatypes) =>
      var locs = locals
        .withSorts(datatypes.map { case (sym, _, _) => sym -> FreshIdentifier(sym.name) })
        .withConstructors(datatypes.flatMap { case (_, _, conss) =>
          conss.map(c => c.sym -> FreshIdentifier(c.sym.name))
        })

      val sorts = for ((sym, tps, conss) <- datatypes) yield {
        val generics = tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos))
        val adtLocals = locs.withGenerics(generics)
        val sortId = locs.getSort(sym)
        val constructors = for (Constructor(c, fields) <- conss) yield {
          val vds = fields.map { case (s, sort) =>
            ValDef.fresh(s.name, adtLocals.extractSort(sort)).setPos(s.optPos)
          }
          locs = locs.withSelectors((fields zip vds).map { case ((s, _), vd) => s -> vd.id })
          new ADTConstructor(locs.getConstructor(c), sortId, vds).setPos(c.optPos)
        }
        val tparams = generics.map { case (s, tp) => TypeParameterDef(tp).setPos(s.optPos) }
        new ADTSort(sortId, tparams, constructors, Seq.empty).setPos(sym.optPos)
      }

      (None, locs.registerSorts(sorts))

    case _: Push | _: Pop =>
      error("push and pop are not supported", cmd.optPos)

    case _ => super.extractCommand(cmd)
  }

  class SMTLIB3Extractor(symbols: Symbols) extends TermExtractor(symbols) {
    import symbols.{given, _}

    private def arity(sym: SSymbol)(using ctx: Context): Int =
      symbols.getFunction(ctx.getFunction(sym)).params.size

    private def isFunctionSymbol(sym: SSymbol)(using ctx: Context): Boolean =
      !ctx.isVariable(sym) && ctx.isFunction(sym)

    /** Applies `caller` to `args`, currying or eta-expanding it when the numbers of arguments differ. */
    private def apply(caller: Expr, args: Seq[Expr], term: Term): Expr = caller.getType match {
      case FunctionType(from, _) if args.size == from.size => Application(caller, args)
      case FunctionType(from, _) if args.size > from.size =>
        apply(Application(caller, args.take(from.size)), args.drop(from.size), term)
      case FunctionType(from, _) =>
        val vds = from.drop(args.size).map(ValDef.fresh("x", _))
        Lambda(vds, Application(caller, args ++ vds.map(_.toVariable)))
      case tpe =>
        error(s"cannot apply $caller of type $tpe to ${args.mkString(", ")}", term.optPos)
    }

    /** The function `fd` instantiated with `tps` and partially applied to `args`. */
    private def partial(fd: FunDef, tps: Seq[Type], args: Seq[Expr]): Expr = {
      val tfd = fd.typed(tps)
      val vds = tfd.params.drop(args.size).map(vd => ValDef.fresh(vd.id.name, vd.getType))
      Lambda(vds, tfd.applied(args ++ vds.map(_.toVariable)))
    }

    private def quantified(binder: String, body: Expr, term: Term): Expr = {
      val (vds, pred) = body match {
        case Lambda(vds, pred) => (vds, pred)
        case _ => body.getType match {
          case FunctionType(from, _) =>
            val vds = from.map(ValDef.fresh("x", _))
            (vds, Application(body, vds.map(_.toVariable)))
          case tpe => error(s"$binder expects a function, found $body of type $tpe", term.optPos)
        }
      }
      binder match {
        case "forall" => Forall(vds, pred)
        case "exists" => Not(Forall(vds, Not(pred)))
        case "choose" => vds match {
          case Seq(vd) => Choose(vd, pred)
          case _ => error(s"choose expects a unary predicate, found $body", term.optPos)
        }
        case _ => error(s"unknown binder $binder", term.optPos)
      }
    }

    override protected def fromSMT(term: Term, otpe: Option[Type] = None)(using ctx: Context): Expr = (term match {
      case VarAnnotation(t, _, _, _, _) => fromSMT(t, otpe)

      case BinderApplication(binder, body) => quantified(binder, fromSMT(body), term)

      case SMTApplication(caller, args) => apply(fromSMT(caller), args.map(fromSMT(_)), term)

      case FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("is"), Seq(c: SSymbol)), None), Seq(t))
      if ctx.isConstructor(c) =>
        IsConstructor(fromSMT(t), ctx.getConstructor(c))

      case Match(scrut, cases) if cases.exists {
        case Case(CaseObject(sym), _) => !ctx.isConstructor(sym)
        case _ => false
      } =>
        // variable patterns bind the scrutinee
        fromSMT(Match(scrut, cases.map {
          case Case(CaseObject(sym), rhs) if !ctx.isConstructor(sym) =>
            Case(Default, SMTLet(VarBinding(sym, scrut), Seq(), rhs))
          case cse => cse
        }).setPos(term), otpe)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args)
      if ctx.isVariable(sym) =>
        apply(ctx.getVariable(sym), args.map(fromSMT(_)), term)

      case QualifiedIdentifier(SimpleIdentifier(sym), optSort) if isFunctionSymbol(sym) && arity(sym) > 0 =>
        val fd = symbols.getFunction(ctx.getFunction(sym))
        val funType = FunctionType(fd.params.map(_.getType), fd.getType)
        val tps = optSort.map(fromSMT(_)).orElse(otpe) match {
          case Some(tpe) if fd.tparams.nonEmpty =>
            instantiateTypeParams(fd.tparams, Seq(funType), Seq(tpe.getType))(using ctx.locals)
          case _ => fd.tparams.map(_.tp)
        }
        partial(fd, tps, Seq.empty)

      case FunctionApplication(qid @ QualifiedIdentifier(SimpleIdentifier(sym), optSort), args)
      if isFunctionSymbol(sym) && args.size != arity(sym) =>
        val fd = symbols.getFunction(ctx.getFunction(sym))
        if (args.size > fd.params.size) {
          val (now, later) = args.splitAt(fd.params.size)
          val call = if (now.isEmpty) fromSMT(qid) else fromSMT(FunctionApplication(qid, now).setPos(term))
          apply(call, later.map(fromSMT(_)), term)
        } else {
          val es = args.map(fromSMT(_))
          val tps = instantiateTypeParams(
            fd.tparams, fd.params.take(es.size).map(_.getType), es.map(_.getType))(using ctx.locals)
          partial(fd, tps, es)
        }

      case _ => super.fromSMT(term, otpe)
    }).setPos(term.optPos)

    private def constant(term: Term)(using Context): Int = term match {
      case SNumeral(n) => n.toInt
      case _ => error(s"unsupported non-constant size $term", term.optPos)
    }

    private def restricted(name: Option[SSymbol], base: Type, restrictions: Seq[Term], term: Term)
                          (using ctx: Context): Type = (name, restrictions) match {
      case (_, Seq()) => base
      case (Some(n), _) =>
        val vd = ValDef.fresh(n.name, base).setPos(n.optPos)
        val newCtx = ctx.withVariable(n, vd.toVariable)
        RefinementType(vd, andJoin(restrictions.map(fromSMT(_, BooleanType())(using newCtx))))
      case (None, _) =>
        error(s"restrictions need a variable (:var) to refer to in $term", term.optPos)
    }

    /** The (possibly dependent) function type `(-> A1 ... An B)`. */
    private def arrowType(types: Seq[Term], term: Term)(using ctx: Context): Type = {
      var context = ctx
      var dependent = false
      val params = types.init.map {
        case va @ VarAnnotation(_, _, true, _, _) =>
          error(s"implicit parameters are not supported in $term", va.optPos)
        case va @ VarAnnotation(base, Some(n), _, restrictions, _) =>
          dependent = true
          val tpe = restricted(Some(n), typeFromTerm(base)(using context), restrictions, va)(using context)
          val vd = ValDef.fresh(n.name, tpe).setPos(n.optPos)
          context = context.withVariable(n, vd.toVariable)
          vd
        case t =>
          val tpe = typeFromTerm(t)(using context)
          if (tpe.isInstanceOf[RefinementType]) dependent = true
          ValDef.fresh("x", tpe).setPos(t.optPos)
      }
      val to = typeFromTerm(types.last)(using context)
      if (dependent) PiType(params, to) else FunctionType(params.map(_.tpe), to)
    }

    /** The type `sym` defined with `define-type`, instantiated with `args`. */
    private def expand(sym: SSymbol, args: Seq[Term], term: Term)(using Context): Type = {
      val TypeDefinition(params, body) = typeDefs(sym)
      if (params.size != args.size) {
        error(s"$sym expects ${params.size} arguments, found ${args.size}", term.optPos)
      }
      val tpSubst = (params zip args).collect { case (Left(tp), arg) => tp -> typeFromTerm(arg) }.toMap
      val vSubst = (params zip args).collect {
        case (Right(v), arg) => v -> fromSMT(arg, typeOps.instantiateType(v.tpe, tpSubst))
      }.toMap
      typeOps.replaceFromSymbols(vSubst, typeOps.instantiateType(body, tpSubst))
    }

    private def isTypeDef(sym: SSymbol)(using ctx: Context): Boolean =
      typeDefs.contains(sym) && !ctx.isGeneric(sym) && !ctx.isSort(sym)

    /** The type that `term` denotes. */
    def typeFromTerm(term: Term)(using ctx: Context): Type = (term match {
      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), types)
      if isArrow(sym) && types.size >= 2 =>
        arrowType(types, term)

      case VarAnnotation(_, _, true, _, _) =>
        error(s"implicit arguments are only supported in function types", term.optPos)

      case VarAnnotation(base, name, _, restrictions, _) =>
        restricted(name, typeFromTerm(base), restrictions, term)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("BitVec")), None), Seq(size)) =>
        BVType(true, constant(size))

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args) if isTypeDef(sym) =>
        expand(sym, args, term)

      case QualifiedIdentifier(SimpleIdentifier(sym), None) if isTypeDef(sym) =>
        expand(sym, Seq.empty, term)

      case _ => TermSort(term) match {
        case _: TermSort => error(s"unsupported type $term", term.optPos)
        case sort => fromSMT(sort)
      }
    }).setPos(term.optPos)

    override protected def fromSMT(sort: Sort)(using ctx: Context): Type = sort match {
      case ts: TermSort => typeFromTerm(ts.term)
      case Sort(SimpleIdentifier(sym), sorts) if (isArrow(sym) && sorts.size >= 2) || isTypeDef(sym) =>
        typeFromTerm(TermSort.toTerm(sort))
      case _ => super.fromSMT(sort)
    }
  }
}

object Parser {
  def apply(file: File): Parser = Parser(new FileReader(file), Some(file))
  def apply(reader: Reader, file: Option[File] = None): Parser = new Parser(reader, file)
}
