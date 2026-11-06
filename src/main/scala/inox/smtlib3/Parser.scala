/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package smtlib3

import smtlib.trees.Commands.{FunDef => SMTFunDef, _}
import smtlib.trees.Terms.{Let => SMTLet, Forall => SMTForall, Identifier => SMTIdentifier, _}
import smtlib.extensions.tip.Terms.{Lambda => SMTLambda, Application => SMTApplication, Match, Case, Default, CaseObject, CaseClass}

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

/** A datatype with value parameters.
  *
  * @param tparams the type parameters of the datatype
  * @param params  the type parameters (`Left`) and value parameters (`Right`, with the function that
  *                returns the parameter of a value, and the parameter's type) in declaration order
  */
private[smtlib3] case class IndexedSort(tparams: Seq[inox.trees.TypeParameter],
                                        params: Seq[Either[inox.trees.TypeParameter, (inox.ast.Identifier, inox.trees.Type)]])

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
  * It also supports the following extensions, which aren't part of the SMT-LIB 3 proposal:
  *
  *  - Tuples in the syntax of cvc5, `(Tuple A B)`, `(tuple a b)` and `((_ tuple.select i) t)`, whose
  *    components may bind variables like the parameters of function types: dependent tuples
  *    `(Tuple (! Int :var n) (! Int :var m :restrict (> m n)))` become Inox `SigmaType`s.
  *  - Dependent datatype fields: field types may refer to the other fields of their constructor and
  *    carry `:restrict` annotations, as Inox ADT fields have dependent types. The `:restrict`
  *    annotations of constructors refine the type of their last field.
  *  - Datatype value parameters `(par (E (! Int :var n)) ...)`. Each constructor stores them in
  *    leading hidden fields, to which the other field types may refer, which constructor
  *    applications take as their first arguments (or from the type in `(as c T)`), and which
  *    patterns omit. The type `(Vec E 3)` is the refinement of the datatype type whose value
  *    parameter is 3.
  *
  * Modules, implicit parameters (`:implicit`) and value-dependent widths aren't supported.
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

  /** The datatypes with value parameters. */
  private var indexedSorts: Map[Identifier, IndexedSort] = Map.empty

  /** The number of leading hidden fields of the constructors of datatypes with value parameters. */
  private var hiddenFields: Map[Identifier, Int] = Map.empty

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

  /** `tpe` without its top-level refinements. */
  private def stripRefinements(tpe: Type): Type = tpe match {
    case RefinementType(vd, _) => stripRefinements(vd.tpe)
    case _ => tpe
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
        .withSorts(datatypes.map(d => d.name -> FreshIdentifier(d.name.name)))
        .withConstructors(datatypes.flatMap(_.constructors.map(c => c.sym -> FreshIdentifier(c.sym.name))))

      // The parameters are known before the fields, which may refer to any of the datatypes
      val headers = for (d <- datatypes) yield {
        val sortId = locs.getSort(d.name)
        var paramLocals = locs
        val params = d.params.map {
          case TypeParam(s) =>
            val tp = TypeParameter.fresh(s.name).setPos(s.optPos)
            paramLocals = paramLocals.withGeneric(s, tp)
            Left(tp)
          case ValueParam(va @ VarAnnotation(base, Some(n), _, restrictions, _)) =>
            Right((n, FreshIdentifier(d.name.name + "$" + n.name), base, restrictions, va))
          case p => error(s"unexpected datatype parameter $p", d.name.optPos)
        }
        val tparams = params.collect { case Left(tp) => tp }
        val valueParams = params.collect { case Right((n, id, base, restrictions, va)) =>
          (n, id, paramLocals.extractSort(TermSort(base).setPos(va)), restrictions)
        }
        if (valueParams.nonEmpty) {
          var vps = valueParams
          indexedSorts += sortId -> IndexedSort(tparams, params.map {
            case Left(tp) => Left(tp)
            case Right(_) =>
              val (_, id, tpe, _) = vps.head
              vps = vps.tail
              Right((id, tpe))
          })
        }
        (d, sortId, tparams, valueParams, paramLocals)
      }

      // The field types may refer to the other fields of their constructor, as Inox ADT fields can
      val sortsAndFuns = for ((d, sortId, tparams, valueParams, paramLocals) <- headers) yield {
        val constructors = for (ConstructorDec(c, fields, restrictions) <- d.constructors) yield {
          var fieldLocals = paramLocals

          val hidden = valueParams.map { case (n, _, tpe, restrictions) =>
            val vd = ValDef.fresh(n.name, tpe).setPos(n.optPos)
            val refined = if (restrictions.isEmpty) vd else {
              val rvd = vd.freshen
              val restrictionLocals = fieldLocals.withVariable(n, rvd.toVariable)
              vd.copy(tpe = RefinementType(rvd, andJoin(restrictions.map(restrictionLocals.extractTerm))))
            }
            fieldLocals = fieldLocals.withVariable(n, refined.toVariable)
            refined
          }

          val vds = fields.map { case (s, sort) =>
            val vd = ValDef.fresh(s.name, fieldLocals.extractSort(sort)).setPos(s.optPos)
            fieldLocals = fieldLocals.withVariable(s, vd.toVariable)
            vd
          }

          // The restrictions of the constructor refine the type of its last field, where all fields are bound
          val allFields = hidden ++ vds
          val restricted = if (restrictions.isEmpty) allFields else allFields.lastOption match {
            case Some(last) =>
              val rvd = last.freshen
              val pred = exprOps.replaceFromSymbols(Map(last.toVariable -> rvd.toVariable),
                andJoin(restrictions.map(fieldLocals.extractTerm)))
              allFields.init :+ last.copy(tpe = RefinementType(rvd, pred))
            case None =>
              error(s"constructor $c has no field to restrict", c.optPos)
          }
          // the references to the last field now refer to its refined version
          val fieldSubst: Map[Variable, Expr] = (allFields zip restricted).collect {
            case (vd, rvd) if vd != rvd => vd.toVariable -> rvd.toVariable
          }.toMap
          val finalFields = restricted.map(vd => vd.copy(tpe = typeOps.replaceFromSymbols(fieldSubst, vd.tpe)))

          locs = locs.withSelectors((fields zip finalFields.drop(hidden.size)).map { case ((s, _), vd) => s -> vd.id })
          val consId = locs.getConstructor(c)
          if (hidden.nonEmpty) hiddenFields += consId -> hidden.size
          (new ADTConstructor(consId, sortId, finalFields).setPos(c.optPos), hidden.size)
        }

        val tparamDefs = tparams.map(tp => TypeParameterDef(tp).setPos(tp))
        val thiss = ValDef.fresh("this", ADTType(sortId, tparams)).setPos(d.name.optPos)

        // The function that returns each value parameter
        val selectors = valueParams.zipWithIndex.map { case ((n, id, tpe, _), i) =>
          val cases = constructors.map { case (cons, _) => cons -> ADTSelector(thiss.toVariable, cons.fields(i).id) }
          val body = cases.init.foldRight(cases.last._2: Expr) { case ((cons, sel), elze) =>
            IfExpr(IsConstructor(thiss.toVariable, cons.id), sel, elze)
          }
          new FunDef(id, tparamDefs, Seq(thiss), tpe, body, Seq.empty).setPos(n.optPos)
        }

        val sort = new ADTSort(sortId, tparamDefs, constructors.map(_._1), Seq.empty).setPos(d.name.optPos)
        (sort, selectors)
      }

      locs = locs.registerSorts(sortsAndFuns.map(_._1))
      (None, locs.withSymbols(locs.symbols.withFunctions(sortsAndFuns.flatMap(_._2))))

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

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("tuple")), None), args)
      if args.size >= 2 && !ctx.isVariable(SSymbol("tuple")) && !ctx.isFunction(SSymbol("tuple")) =>
        Tuple(args.map(fromSMT(_)))

      case FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("tuple.select"), Seq(SNumeral(i))), None), Seq(t)) =>
        TupleSelect(fromSMT(t), i.toInt + 1)

      case QualifiedIdentifier(SimpleIdentifier(sym), Some(sort)) if ctx.isConstructor(sym) && !ctx.isVariable(sym) =>
        construct(sym, sort, Seq.empty, term)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), Some(sort)), args)
      if ctx.isConstructor(sym) && !ctx.isVariable(sym) =>
        construct(sym, sort, args, term)

      case QualifiedIdentifier(SimpleIdentifier(sym), None) if hidden(sym) > 0 && !ctx.isVariable(sym) =>
        error(s"constructor $sym needs the values of its datatype's parameters, e.g. with (as $sym T)", term.optPos)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args)
      if hidden(sym) > 0 && !ctx.isVariable(sym) &&
         args.size != symbols.getConstructor(ctx.getConstructor(sym)).fields.size =>
        error(s"constructor $sym takes the values of its datatype's parameters first, or use (as $sym T)", term.optPos)

      case Match(scrut, cases) if cases.exists {
        case Case(CaseClass(sym, binders), _) =>
          hidden(sym) > 0 && binders.size + hidden(sym) == symbols.getConstructor(ctx.getConstructor(sym)).fields.size
        case _ => false
      } =>
        // patterns omit the hidden fields
        fromSMT(Match(scrut, cases.map {
          case Case(CaseClass(sym, binders), rhs)
          if hidden(sym) > 0 && binders.size + hidden(sym) == symbols.getConstructor(ctx.getConstructor(sym)).fields.size =>
            Case(CaseClass(sym, List.tabulate(hidden(sym))(i => SSymbol(FreshIdentifier("hidden").uniqueName)) ++ binders), rhs)
          case cse => cse
        }).setPos(term), otpe)

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

    /** The (possibly dependent) types `(A1 ... An B)` of function parameters and results, or of tuples.
      *
      * The types `Ai` may bind variables with `(! Ai :var x)`, to which the next types may refer.
      * @return whether the types are dependent, the `Ai` and `B` */
    private def telescope(types: Seq[Term], term: Term)(using ctx: Context): (Boolean, Seq[ValDef], Type) = {
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
      (dependent, params, typeFromTerm(types.last)(using context))
    }

    /** The (possibly dependent) function type `(-> A1 ... An B)`. */
    private def arrowType(types: Seq[Term], term: Term)(using Context): Type = telescope(types, term) match {
      case (true, params, to) => PiType(params, to)
      case (false, params, to) => FunctionType(params.map(_.tpe), to)
    }

    /** The (possibly dependent) tuple type `(Tuple A1 ... An B)`. */
    private def tupleType(types: Seq[Term], term: Term)(using Context): Type = telescope(types, term) match {
      case (true, params, to) => SigmaType(params, to)
      case (false, params, to) => TupleType(params.map(_.tpe) :+ to)
    }

    private def indexedSort(sym: SSymbol)(using ctx: Context): Option[(Identifier, IndexedSort)] =
      if (ctx.isGeneric(sym) || !ctx.isSort(sym)) None
      else indexedSorts.get(ctx.getSort(sym)).map(ctx.getSort(sym) -> _)

    /** The type arguments and the value arguments of the datatype `id` with value parameters. */
    private def indexedArgs(id: Identifier, is: IndexedSort, args: Seq[Term], term: Term)
                           (using Context): (Seq[Type], Option[Seq[(Identifier, Expr)]]) = {
      val nTypes = is.params.count(_.isLeft)
      if (args.size == nTypes) {
        (args.map(typeFromTerm), None)
      } else if (args.size == is.params.size) {
        val tps = (is.params zip args).collect { case (Left(_), arg) => typeFromTerm(arg) }
        val tpSubst: Map[TypeParameter, Type] = (is.tparams zip tps).toMap
        val values = (is.params zip args).collect { case (Right((fid, tpe)), arg) =>
          fid -> fromSMT(arg, typeOps.instantiateType(tpe, tpSubst))
        }
        (tps, Some(values))
      } else {
        error(s"${id.name} expects ${nTypes} type arguments, or ${is.params.size} arguments", term.optPos)
      }
    }

    /** The type `(S T1 ... v1 ...)` of the datatype `S` with value parameters, whose values are the
      * values of `S` whose value parameters are `v1 ...`. */
    private def indexedType(id: Identifier, is: IndexedSort, args: Seq[Term], term: Term)(using Context): Type = {
      indexedArgs(id, is, args, term) match {
        case (tps, None) => ADTType(id, tps)
        case (tps, Some(values)) =>
          val vd = ValDef.fresh(id.name.toLowerCase, ADTType(id, tps))
          RefinementType(vd, andJoin(values.map { case (fid, v) =>
            Equals(FunctionInvocation(fid, tps, Seq(vd.toVariable)), v)
          }))
      }
    }

    /** The values of the hidden fields of constructors of the datatype type `sort`. */
    private def hiddenValues(sort: Sort, term: Term)(using ctx: Context): Option[Seq[Expr]] =
      TermSort.toTerm(sort) match {
        case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args) =>
          indexedSort(sym).flatMap { case (id, is) => indexedArgs(id, is, args, term)._2.map(_.map(_._2)) }
        case _ => None
      }

    private def hidden(sym: SSymbol)(using ctx: Context): Int =
      if (ctx.isConstructor(sym)) hiddenFields.getOrElse(ctx.getConstructor(sym), 0) else 0

    /** Applies the constructor `sym` of the datatype type `sort` to `args`, after its hidden fields. */
    private def construct(sym: SSymbol, sort: Sort, args: Seq[Term], term: Term)(using ctx: Context): Expr = {
      val cons = symbols.getConstructor(ctx.getConstructor(sym))
      val tps = stripRefinements(fromSMT(sort)) match {
        case ADTType(_, tps) => tps
        case tpe => error(s"unexpected type $tpe for constructor $sym", term.optPos)
      }
      val tcons = cons.typed(tps)
      val hiddenArgs = if (args.size + hidden(sym) == cons.fields.size && hidden(sym) > 0) {
        hiddenValues(sort, term).getOrElse(error(s"missing values of the parameters of $sym in $term", term.optPos))
      } else Seq.empty
      val es = hiddenArgs ++ (args zip tcons.fields.drop(hiddenArgs.size)).map { case (a, vd) => fromSMT(a, vd.getType) }
      ADT(cons.id, tps, es)
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

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("Tuple")), None), types)
      if types.size >= 2 && !ctx.isSort(SSymbol("Tuple")) =>
        tupleType(types, term)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args) if indexedSort(sym).isDefined =>
        val Some((id, is)) = indexedSort(sym): @unchecked
        indexedType(id, is, args, term)

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
      case Sort(SimpleIdentifier(sym), sorts)
      if (isArrow(sym) && sorts.size >= 2) || (sym.name == "Tuple" && sorts.size >= 2 && !ctx.isSort(sym)) ||
         isTypeDef(sym) || (sorts.nonEmpty && indexedSort(sym).isDefined) =>
        typeFromTerm(TermSort.toTerm(sort))
      case _ => super.fromSMT(sort)
    }
  }
}

object Parser {
  def apply(file: File): Parser = Parser(new FileReader(file), Some(file))
  def apply(reader: Reader, file: Option[File] = None): Parser = new Parser(reader, file)
}
