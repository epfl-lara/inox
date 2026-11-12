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

/** Parses SMT-LIB 3 scripts (see https://smt-lib.org/version3.shtml) into Inox programs.
  *
  * The parser extends the TIP parser of [[inox.tip.Parser]], so it also accepts TIP inputs and the
  * Inox extensions to it (e.g. `datatype-invariant` and `assume`). On top of these, it
  * supports the following SMT-LIB 3 features:
  *
  *  - Function types `(-> A B C)` (also spelled `→`), and dependent function types whose parameters
  *    bind variables with `(! A :var x)`, which become Inox `PiType`s.
  *  - Predicate subtypes `(! A :var x :restrict p)`, which become Inox `RefinementType`s.
  *  - Rank-1 polymorphism through global type variables (`declare-type-var`): the declarations
  *    and definitions that mention type variables become polymorphic functions.
  *  - `declare-type`, and `define-type` with type and value parameters. Types declared without
  *    parameters (also with `declare-sort`) are uninterpreted and become Inox type parameters.
  *  - `define-const` and `define-const-rec`. Non-recursive definitions may refer to the declared
  *    constants, and are then expanded where they are used.
  *  - `push` and `pop`, and the `set-info` and `set-option` attributes of each query, see
  *    [[inox.tip.Parser.parseQueries]].
  *  - Curried and partial applications of functions, and the higher-order forms of the binders,
  *    e.g. `(forall p)` or `(exists (lambda ((x Int)) (> x 0)))`.
  *  - `declare-fun` with named parameters `(declare-fun f ((x A)) B)`, whose result sort `B` may
  *    refer to them.
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
  *  - Unsigned bit-vector types `(! (_ BitVec 8) :unsigned)`, and the casts `(! t :unsigned)` and
  *    `(! t :signed)` between signed and unsigned bit-vectors. Bit-vector types are signed by
  *    default. The SMT-LIB operations keep their semantics whatever the signedness of their
  *    operands, e.g. `bvudiv` of signed bit-vectors is an unsigned division.
  *  - Characters `Char`, whose literals are 16-bit vectors annotated with `:char`, as in
  *    `(! #x0041 :char)`, and the unit type `UnitTuple` and value `tuple.unit` of cvc5.
  *  - Custom datatype equalities `(datatype-equality S f)`, where `f` is a function from two values
  *    of `S` to `Bool`, which Inox uses as the equality of `S`.
  *
  * The [[Printer]] prints Inox programs in this syntax.
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

  override protected def saveScope(): Any = (typeVars, typeDefs)
  override protected def restoreScope(state: Any): Unit = state match {
    case (tvs: Seq[TypeParameter] @unchecked, tds: Map[SSymbol, TypeDefinition] @unchecked) =>
      typeVars = tvs
      typeDefs = tds
  }

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

    val body = exprOps.uninterpretedBody(id.name, tparams, params, returnType)
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

    val tparams = tps.map(TypeParameterDef(_))
    val body = exprOps.uninterpretedBody(sym.name, tparams, params, returnType)
    new FunDef(FreshIdentifier(sym.name), tparams, params, returnType, body, Seq.empty)
      .setPos(sym.optPos)
  }

  /** `tpe` without its top-level refinements. */
  private def stripRefinements(tpe: Type): Type = tpe match {
    case RefinementType(vd, _) => stripRefinements(vd.tpe)
    case _ => tpe
  }

  /** A parameter `(x S)` whose sort `S` isn't a plain sort, which parses as a term. */
  private object NamedParam {
    def unapply(sort: Sort): Option[(SSymbol, Term)] = sort match {
      case ts: TermSort => ts.term match {
        case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), Seq(inner)) => Some((sym, inner))
        case _ => None
      }
      case _ => None
    }
  }

  /** The parameters of a `declare-fun` that names them, as `((x S) ...)`, which parses as sorts
    * `x` applied to `S` that aren't sorts. */
  private def namedParams(sorts: Seq[Sort])(using locals: Locals): Option[Seq[SortedVar]] = {
    val params = sorts.collect {
      case sort @ Sort(SimpleIdentifier(sym), Seq(inner))
          if scala.util.Try(locals.extractSort(sort)).isFailure => SortedVar(sym, inner).setPos(sort)
      case sort @ NamedParam(sym, inner) if scala.util.Try(locals.extractSort(sort)).isFailure =>
        SortedVar(sym, TermSort(inner)).setPos(sort)
    }
    if (sorts.nonEmpty && params.size == sorts.size) Some(params) else None
  }

  override protected def extractCommand(cmd: Command)(using locals: Locals): (Option[Expr], Locals) = cmd match {
    case _: SetLogic | _: SetInfo | _: SetOption | _: GetModel | _: GetInfo | _: GetValue |
         _: GetAssertions | _: GetAssignment | _: GetUnsatCore | _: GetProof | _: Echo | _: Exit =>
      (None, locals)

    // `(declare-fun f ((x S) ...) R)` names the parameters of `f`, which `R` may refer to
    case DeclareFun(name, sorts, returnSort) if namedParams(sorts).isDefined =>
      (None, locals.withFunction(name, extractSignature(FunDec(name, namedParams(sorts).get, returnSort), Seq.empty)))

    case smtlib.extensions.tip.Commands.DeclareFunPar(tps, name, sorts, returnSort) =>
      // The sorts of the parameters may refer to the type parameters
      val tpsLocals = locals.withGenerics(tps.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos)))
      namedParams(sorts)(using tpsLocals) match {
        case Some(params) =>
          (None, locals.withFunction(name, extractSignature(FunDec(name, params, returnSort), tps)(using tpsLocals)))
        case None => super.extractCommand(cmd)
      }

    case DeclareTypeVar(sym) =>
      val tp = TypeParameter.fresh(sym.name).setPos(sym.optPos)
      typeVars :+= tp
      (None, locals.withGeneric(sym, tp))

    case DeclareType(sym, kinds) =>
      for (kind <- kinds) kind match {
        case Sort(SimpleIdentifier(SSymbol("Type")), Seq()) =>
        case _ => error(s"unsupported kind $kind of $sym (only types of kind Type can be declared)", kind.optPos)
      }
      extractCommand(DeclareSort(sym, kinds.size).setPos(cmd))

    case DeclareSort(sym, 0) =>
      // Uninterpreted types may be finite, as type parameters, unlike the TIP encoding of declared
      // sorts as datatypes that wrap an integer
      (None, locals.withGeneric(sym, TypeParameter.fresh(sym.name).setPos(sym.optPos)))

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
      extractCommand((if (isRec) DefineFunRec(funDef) else DefineFun(funDef)).setPos(cmd))

    case DeclareDatatypesWithPars(datatypes) =>
      // The constructors, fields and selectors are known before the field types, which may refer to them
      var locs = locals
        .withSorts(datatypes.map(d => d.name -> FreshIdentifier(d.name.name)))
        .withConstructors(datatypes.flatMap(_.constructors.map(c => c.sym -> FreshIdentifier(c.sym.name))))
      val fieldIds = datatypes.flatMap(_.constructors.map(c => c.sym -> c.fields.map(f => FreshIdentifier(f._1.name)))).toMap
      locs = locs.withSelectors(datatypes.flatMap(_.constructors.flatMap(c => c.fields.map(_._1) zip fieldIds(c.sym))))

      val sorts = for (d <- datatypes) yield {
        val tparams = d.params.map(s => s -> TypeParameter.fresh(s.name).setPos(s.optPos))
        val paramLocals = locs.withGenerics(tparams)

        // The field types may refer to the previous fields of their constructor, as Inox ADT fields can
        val constructors = for (ConstructorDec(c, fields, restrictions) <- d.constructors) yield {
          var fieldLocals = paramLocals
          val vds = (fields zip fieldIds(c)).map { case ((s, sort), id) =>
            val vd = ValDef(id, fieldLocals.extractSort(sort)).setPos(s.optPos)
            fieldLocals = fieldLocals.withVariable(s, vd.toVariable)
            vd
          }

          // The restrictions of the constructor refine the type of its last field, where all fields are bound
          val finalFields = if (restrictions.isEmpty) vds else vds.lastOption match {
            case Some(last) =>
              val rvd = last.freshen
              val pred = exprOps.replaceFromSymbols(Map(last.toVariable -> rvd.toVariable),
                andJoin(restrictions.map(fieldLocals.extractTerm)))
              vds.init :+ last.copy(tpe = RefinementType(rvd, pred))
            case None =>
              error(s"constructor $c has no field to restrict", c.optPos)
          }

          new ADTConstructor(locs.getConstructor(c), locs.getSort(d.name), finalFields).setPos(c.optPos)
        }

        val tparamDefs = tparams.map(p => TypeParameterDef(p._2).setPos(p._2))
        new ADTSort(locs.getSort(d.name), tparamDefs, constructors, Seq.empty).setPos(d.name.optPos)
      }

      (None, locs.registerSorts(sorts))

    case DatatypeEquality(sortSym, funSym) =>
      if (!locals.isSort(sortSym)) error(s"unknown datatype $sortSym", sortSym.optPos)
      if (!locals.isFunction(funSym)) error(s"unknown function $funSym", funSym.optPos)
      val sort = locals.symbols.getSort(locals.getSort(sortSym))
      val fd = locals.symbols.getFunction(locals.getFunction(funSym))
      val tpe = ADTType(sort.id, fd.tparams.map(_.tp))
      if (fd.tparams.size != sort.tparams.size || fd.params.map(_.getType(using locals.symbols)) != Seq(tpe, tpe) ||
          fd.getType(using locals.symbols) != BooleanType()) {
        error(s"the equality $funSym of $sortSym should take two values of type $tpe and return a Bool", funSym.optPos)
      }
      val newSort = sort.copy(flags = sort.flags.filter { case HasADTEquality(_) => false case _ => true } :+ HasADTEquality(fd.id))
      (None, locals.withSymbols(locals.symbols.withSorts(Seq(newSort))))

    case DefineFun(funDef) =>
      val fd = extractFunction(funDef, Seq.empty)
      val params = fd.params.map(_.toVariable).toSet
      val captured = (exprOps.variablesOf(fd.fullBody) ++
        (fd.params.map(_.tpe) :+ fd.returnType).flatMap(typeOps.variablesOf)) -- params
      if (captured.isEmpty) {
        (None, locals.withFunction(funDef.name, fd))
      } else if (fd.tparams.nonEmpty) {
        error(s"polymorphic definition ${funDef.name} can't refer to the constants ${captured.mkString(", ")}", funDef.name.optPos)
      } else {
        // Inox functions can't refer to the declared constants, which are free variables, so the
        // definition is a macro: a value, or a lambda that is applied where the definition is used
        val value = if (fd.params.isEmpty) fd.fullBody else Lambda(fd.params, fd.fullBody)
        (None, locals.withVariable(funDef.name, value.setPos(funDef.name.optPos)))
      }

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
        case _ => error(s"unknown binder $binder", term.optPos)
      }
    }

    private def isFree(sym: String)(using ctx: Context): Boolean =
      !ctx.isVariable(SSymbol(sym)) && !ctx.isFunction(SSymbol(sym)) && !ctx.isConstructor(SSymbol(sym))

    private def bvSignedness(e: Expr): Option[Boolean] = e.getType match {
      case BVType(signed, _) => Some(signed)
      case _ => None
    }

    /** The bit-vector `e` viewed as a signed (or unsigned) bit-vector. */
    private def withSignedness(e: Expr, signed: Boolean): Expr = e match {
      case BVLiteral(s, bits, size) if s != signed => BVLiteral(signed, bits, size)
      case _ => e.getType match {
        case BVType(s, _) if s != signed => if (signed) BVUnsignedToSigned(e) else BVSignedToUnsigned(e)
        case _ => e
      }
    }

    /** The operands `t1` and `t2` of a binary operation, of the same type. Bit-vector literals
      * without expected type are signed, so they take the signedness of the other operand. */
    private def operands(t1: Term, t2: Term, otpe: Option[Type])(using Context): (Expr, Expr) = {
      var res: (Expr, Expr) = null
      fromSMTUnifyType(t1, t2, otpe) { (a, b) => res = (a, b); a }
      res match {
        case (a, b: BVLiteral) if bvSignedness(a).exists(_ != b.signed) => (a, withSignedness(b, !b.signed))
        case (a: BVLiteral, b) if bvSignedness(b).exists(_ != a.signed) => (withSignedness(a, !a.signed), b)
        case p => p
      }
    }

    /** The bit-vector operations whose semantics don't depend on the signedness of their operands. */
    private val bvOps: Map[String, (Expr, Expr) => Expr] = Map(
      "=" -> (Equals(_, _)), "bvadd" -> (Plus(_, _)), "bvsub" -> (Minus(_, _)), "bvmul" -> (Times(_, _)),
      "bvand" -> (BVAnd(_, _)), "bvor" -> (BVOr(_, _)), "bvxor" -> (BVXor(_, _)),
      "bvshl" -> (BVShiftLeft(_, _)), "bvashr" -> (BVAShiftRight(_, _)), "bvlshr" -> (BVLShiftRight(_, _)))

    /** The bit-vector operation `op`, whose semantics depend on the signedness of its operands, as
      * a signed (or unsigned) operation on operands `t1` and `t2` of any signedness. Inox picks the
      * signed or unsigned SMT-LIB operation from the type of the operands, so operands of the other
      * signedness are cast to `signed`, and so is the result back if `isArith`. */
    private def bvOp(signed: Boolean, isArith: Boolean, t1: Term, t2: Term, otpe: Option[Type])
                    (op: (Expr, Expr) => Expr)(using Context): Expr = {
      val (a, b) = operands(t1, t2, if (isArith) otpe else None)
      bvSignedness(a) match {
        case Some(s) if s != signed =>
          val res = op(withSignedness(a, signed), withSignedness(b, signed))
          if (isArith) withSignedness(res, s) else res
        case _ => op(a, b)
      }
    }

    /** `((_ zero_extend n) e)` (or `sign_extend`) for operands `e` of any signedness. */
    private def extend(n: BigInt, t: Term, signedExt: Boolean)(using Context): Expr = {
      val e = fromSMT(t)
      e.getType match {
        case BVType(signed, size) =>
          val newSize = size + n.toInt
          withSignedness(BVWideningCast(withSignedness(e, signedExt), BVType(signedExt, newSize)), signed)
        case tpe => error(s"expected a bit-vector, found $e of type $tpe", t.optPos)
      }
    }

    private def fromSMTExtension(term: Term, otpe: Option[Type])(using ctx: Context): Option[Expr] = {
      import smtlib.theories.{FixedSizeBitVectors => BV}
      import smtlib.theories.{Core, Ints}
      Some(term match {
        case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol(op)), None), Seq(t1, t2))
        if bvOps.contains(op) && isFree(op) =>
          val (a, b) = operands(t1, t2, if (op == "=") None else otpe)
          if (bvSignedness(a).isEmpty && op != "=") return None
          bvOps(op)(a, b)

        case BV.SDiv(t1, t2) => bvOp(true, true, t1, t2, otpe)(Division(_, _))
        case BV.UDiv(t1, t2) => bvOp(false, true, t1, t2, otpe)(Division(_, _))
        case BV.SRem(t1, t2) => bvOp(true, true, t1, t2, otpe)(Remainder(_, _))
        case BV.URem(t1, t2) => bvOp(false, true, t1, t2, otpe)(Remainder(_, _))
        case BV.SMod(t1, t2) => bvOp(true, true, t1, t2, otpe)(Modulo(_, _))
        case BV.SLessThan(t1, t2) => bvOp(true, false, t1, t2, otpe)(LessThan(_, _))
        case BV.SLessEquals(t1, t2) => bvOp(true, false, t1, t2, otpe)(LessEquals(_, _))
        case BV.SGreaterThan(t1, t2) => bvOp(true, false, t1, t2, otpe)(GreaterThan(_, _))
        case BV.SGreaterEquals(t1, t2) => bvOp(true, false, t1, t2, otpe)(GreaterEquals(_, _))
        case BV.ULessThan(t1, t2) => bvOp(false, false, t1, t2, otpe)(LessThan(_, _))
        case BV.ULessEquals(t1, t2) => bvOp(false, false, t1, t2, otpe)(LessEquals(_, _))
        case BV.UGreaterThan(t1, t2) => bvOp(false, false, t1, t2, otpe)(GreaterThan(_, _))
        case BV.UGreaterEquals(t1, t2) => bvOp(false, false, t1, t2, otpe)(GreaterEquals(_, _))

        case BV.BV2Nat(t) => BVToInt(withSignedness(fromSMT(t), false))
        case BV.Int2BV(size, t) =>
          val signed = otpe match {
            case Some(BVType(signed, _)) => signed
            case _ => true
          }
          IntToBV(size.toInt, signed, fromSMT(t, IntegerType()))

        case BV.ZeroExtend(n, t) => extend(n, t, false)
        case BV.SignExtend(n, t) => extend(n, t, true)

        case BV.Extract(i, j, t) =>
          val e = fromSMT(t)
          e.getType match {
            case BVType(signed, size) =>
              val shifted = if (j == 0) e else BVLShiftRight(e, BVLiteral(signed, j, size))
              if (i + 1 - j == size) shifted else BVNarrowingCast(shifted, BVType(signed, (i + 1 - j).toInt))
            case tpe => error(s"expected a bit-vector, found $e of type $tpe", term.optPos)
          }

        case AnnotatedTerm(t, Attribute(SKeyword(kw @ ("signed" | "unsigned")), None), Seq()) =>
          val signed = kw == "signed"
          val e = fromSMT(t, otpe.map {
            case BVType(_, size) => BVType(signed, size)
            case tpe => tpe
          })
          bvSignedness(e) match {
            case Some(_) => withSignedness(e, signed)
            case None => error(s"expected a bit-vector, found $e of type ${e.getType}", term.optPos)
          }

        case AnnotatedTerm(t, Attribute(SKeyword("char"), None), Seq()) =>
          fromSMT(t, CharType())

        case _ => return None
      })
    }

    override protected def fromSMT(term: Term, otpe: Option[Type] = None)(using ctx: Context): Expr = fromSMTExtension(term, otpe).getOrElse(term match {
      case VarAnnotation(t, _, _, _, _) => fromSMT(t, otpe)

      case QualifiedIdentifier(SimpleIdentifier(SSymbol("tuple.unit")), None) if isFree("tuple.unit") =>
        UnitLiteral()

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
      if ctx.isVariable(sym) && !(ctx.isSelector(sym) && !ctx.getVariable(sym).getType.isInstanceOf[FunctionType]) =>
        // in datatype declarations, fields are both variables and selectors
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

    /** Applies the constructor `sym`, of the datatype type `sort`, to `args`. */
    private def construct(sym: SSymbol, sort: Sort, args: Seq[Term], term: Term)(using ctx: Context): Expr = {
      val cons = symbols.getConstructor(ctx.getConstructor(sym))
      val tps = stripRefinements(fromSMT(sort)) match {
        case ADTType(_, tps) => tps
        case tpe => error(s"unexpected type $tpe for constructor $sym", term.optPos)
      }
      val tcons = cons.typed(tps)
      ADT(cons.id, tps, (args zip tcons.fields).map { case (a, vd) => fromSMT(a, vd.getType) })
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
      if isArrow(sym) && types.nonEmpty =>
        arrowType(types, term)

      case VarAnnotation(_, _, true, _, _) =>
        error(s"implicit arguments are only supported in function types", term.optPos)

      case VarAnnotation(base, name, _, restrictions, _) =>
        restricted(name, typeFromTerm(base), restrictions, term)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("Tuple")), None), types)
      if types.size >= 2 && !ctx.isSort(SSymbol("Tuple")) =>
        tupleType(types, term)

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("BitVec")), None), Seq(size)) =>
        BVType(true, constant(size))

      case AnnotatedTerm(base, Attribute(SKeyword(kw @ ("signed" | "unsigned")), None), Seq()) =>
        typeFromTerm(base) match {
          case BVType(_, size) => BVType(kw == "signed", size)
          case tpe => error(s"only bit-vector types can be $kw, found $tpe", term.optPos)
        }

      case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(sym), None), args) if isTypeDef(sym) =>
        expand(sym, args, term)

      case QualifiedIdentifier(SimpleIdentifier(sym), None) if isTypeDef(sym) =>
        expand(sym, Seq.empty, term)

      case FunctionApplication(QualifiedIdentifier(id, None), args) if TermSort(term).isInstanceOf[TermSort] &&
          args.exists(arg => TermSort(arg).isInstanceOf[TermSort]) =>
        // Some arguments aren't plain sorts, e.g. `(Set (! Int :var x :restrict (> x 0)))`: they are
        // replaced by type parameters, which are then instantiated with their types
        var argCtx = ctx
        var subst = Map.empty[TypeParameter, Type]
        val newArgs = args.map { arg =>
          TermSort(arg) match {
            case _: TermSort =>
              val tp = TypeParameter.fresh("T")
              val sym = SSymbol(tp.id.uniqueName)
              subst += tp -> typeFromTerm(arg)
              argCtx = Context(argCtx.locals.withGeneric(sym, tp))
              QualifiedIdentifier(SimpleIdentifier(sym), None)
            case _ => arg
          }
        }
        typeOps.instantiateType(typeFromTerm(FunctionApplication(QualifiedIdentifier(id, None), newArgs))(using argCtx), subst)

      case _ => TermSort(term) match {
        case _: TermSort => error(s"unsupported type $term", term.optPos)
        case sort => fromSMT(sort)
      }
    }).setPos(term.optPos)

    override protected def fromSMT(sort: Sort)(using ctx: Context): Type = sort match {
      case ts: TermSort => typeFromTerm(ts.term)
      case Sort(SimpleIdentifier(sym @ SSymbol("Char" | "UnitTuple")), Seq()) if !ctx.isSort(sym) && !isTypeDef(sym) =>
        if (sym.name == "Char") CharType() else UnitType()
      case Sort(SimpleIdentifier(sym), sorts)
      if (isArrow(sym) && sorts.nonEmpty) || (sym.name == "Tuple" && sorts.size >= 2 && !ctx.isSort(sym)) ||
         isTypeDef(sym) =>
        typeFromTerm(TermSort.toTerm(sort))
      case _ => super.fromSMT(sort)
    }
  }
}

object Parser {
  def apply(file: File): Parser = Parser(new FileReader(file), Some(file))
  def apply(reader: Reader, file: Option[File] = None): Parser = new Parser(reader, file)
}
