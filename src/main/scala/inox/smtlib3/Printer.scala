/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package smtlib3

import smtlib.trees.Terms.{Forall => SMTForall, Identifier => SMTIdentifier, _}
import smtlib.trees.Commands.{FunDef => SMTFunDef, _}
import smtlib.extensions.tip.Terms.{Lambda => SMTLambda, FunDecPar}
import smtlib.extensions.tip.Commands._
import smtlib.printer.PrintingContext
import inox.tip.Bags
import smtlib.theories.cvc.{CVC4Sets => Sets}

import inox.tip.Terms.{Choose => SMTChoose}
import inox.tip.Commands.{DatatypeInvariant, DatatypeInvariantPar}

import Terms._
import Commands._

import java.io.Writer

/** Prints Inox programs in the SMT-LIB 3 syntax that [[Parser]] reads.
  *
  * The printer extends the TIP printer of [[inox.tip.Printer]], and prints the Inox features that
  * TIP doesn't express in the syntax of [[Parser]]:
  *
  *  - Dependent function types (`PiType`) as `(-> (! A :var x) B)`, dependent tuple types
  *    (`SigmaType`) as `(Tuple (! A :var x) B)` and refinement types as `(! A :var x :restrict p)`,
  *    including in the parameters and results of functions, and in the fields of datatypes.
  *  - Tuples as `(Tuple A B)`, `(tuple a b)` and `((_ tuple.select i) t)`, and the unit type and
  *    value as `UnitTuple` and `tuple.unit`.
  *  - Unsigned bit-vector types as `(! (_ BitVec n) :unsigned)`, the casts between signed and
  *    unsigned bit-vectors as `(! t :unsigned)` and `(! t :signed)`, and unsigned bit-vector
  *    literals as `(! #x01 :unsigned)`.
  *  - Characters as `Char`, and character literals as `(! #x0041 :char)`.
  *  - Custom datatype equalities as `(datatype-equality S f)`.
  */
class Printer(prog: InoxProgram, ctx: inox.Context, writer: Writer) extends tip.Printer(prog, ctx, writer) {
  import program.trees._
  import program.symbols.{given, _}

  override def targetName = "smtlib3"

  override protected def printingContext(writer: Writer): PrintingContext = new PrintingContext(writer) {
    override def print(tree: smtlib.trees.Tree): Unit = tree match {
      case ts: TermSort => print(ts.term)
      case _ => super.print(tree)
    }
  }

  private def keyword(term: Term, kw: String): Term = AnnotatedTerm(term, Attribute(SKeyword(kw)), Seq())

  private def sym(name: String): SMTIdentifier = SimpleIdentifier(SSymbol(name))

  /** The sorts of a telescope of (possibly dependent) parameters followed by the type `to`, where
    * each parameter binds a variable to which the next types refer. */
  private def telescope(params: Seq[ValDef], to: Type)(using bindings: Map[Identifier, Term]): Seq[Sort] = {
    var current = bindings
    val sorts = params.map { vd =>
      val s = id2sym(vd.id)
      val sort = binder(vd, s)(using current)
      current += vd.id -> s
      sort
    }
    sorts :+ sortOf(to)(using current)
  }

  /** The sort `(! A :var s :restrict p)` of the parameter `vd`, which binds `s`. */
  private def binder(vd: ValDef, s: SSymbol)(using bindings: Map[Identifier, Term]): Sort = vd.tpe match {
    case RefinementType(rvd, pred) =>
      val base = TermSort.toTerm(sortOf(rvd.tpe))
      val restriction = toSMT(pred)(using bindings + (rvd.id -> s))
      new TermSort(VarAnnotation(base, Some(s), false, Seq(restriction), Seq()))
    case tpe =>
      new TermSort(VarAnnotation(TermSort.toTerm(sortOf(tpe)), Some(s), false, Seq(), Seq()))
  }

  /** The sort of the type `t`, whose refinements may refer to the variables in `bindings`. */
  protected def sortOf(t: Type)(using bindings: Map[Identifier, Term]): Sort = t match {
    case RefinementType(vd, pred) =>
      val s = id2sym(vd.id)
      val base = TermSort.toTerm(sortOf(vd.tpe))
      new TermSort(VarAnnotation(base, Some(s), false, Seq(toSMT(pred)(using bindings + (vd.id -> s))), Seq()))

    case PiType(params, to) =>
      Sort(sym("->"), telescope(params, to))

    case SigmaType(params, to) =>
      Sort(sym("Tuple"), telescope(params, to))

    case FunctionType(from, to) =>
      Sort(sym("->"), (from :+ to).map(sortOf))

    case TupleType(ts) =>
      Sort(sym("Tuple"), ts.map(sortOf))

    case UnitType() =>
      Sort(sym("UnitTuple"))

    case BVType(true, size) =>
      Sort(SMTIdentifier(SSymbol("BitVec"), Seq(SNumeral(size))))

    case BVType(false, size) =>
      new TermSort(keyword(QualifiedIdentifier(SMTIdentifier(SSymbol("BitVec"), Seq(SNumeral(size)))), "unsigned"))

    case CharType() =>
      Sort(sym("Char"))

    case MapType(from, to) =>
      Sort(sym("Array"), Seq(sortOf(from), sortOf(to)))

    case SetType(base) =>
      Sets.SetSort(sortOf(base))

    case BagType(base) =>
      Bags.BagSort(sortOf(base))

    case adt: ADTType =>
      val lifted = liftADTType(adt)
      adtManager.declareADTs(lifted, declareDatatypes)
      val Sort(id, _) = sorts.toB(lifted)
      Sort(id, adt.tps.map(sortOf))

    case tp: TypeParameter =>
      Sort(SMTIdentifier(id2sym(tp.id)))

    case _ => super.computeSort(t)
  }

  override protected def computeSort(t: Type): Sort = sortOf(t)(using Map.empty)

  override protected def declareDatatypes(datatypes: Seq[(Type, DataType)]): Unit = {
    // Tuples and the unit type are built in, and type parameters are declared by the datatypes
    val adts = datatypes
      .collect { case (ADTType(id, _), dt) => (getSort(id), dt) }
      .groupBy(_._1.id).values.map(_.head).toSeq
      .filterNot { case (sort, _) => sorts.containsA(ADTType(sort.id, sort.typeArgs)) }
      .sortBy(_._1.id.globalId)

    // The field types may refer to the constructors, selectors and testers of these datatypes
    for ((sort, DataType(dsym, cases)) <- adts) {
      sorts += ADTType(sort.id, sort.typeArgs) -> Sort(SMTIdentifier(id2sym(dsym)), sort.typeArgs.map(sortOf(_)(using Map.empty)))
      for ((c, cons) <- cases zip sort.constructors) {
        val s = id2sym(c.sym)
        val ctpe = ADTCons(cons.id, sort.typeArgs)
        testers += ctpe -> SSymbol("is-" + s.name)
        constructors += ctpe -> s
        for (((fs, _), i) <- c.fields.zipWithIndex) selectors += (ctpe, i) -> id2sym(fs)
      }
    }

    if (adts.nonEmpty) {
      emit(DeclareDatatypesWithPars(for ((sort, DataType(dsym, cases)) <- adts) yield {
        DatatypeDec(id2sym(dsym), sort.typeArgs.map(tp => TypeParam(id2sym(tp.id))), (cases zip sort.constructors).map {
          case (c, cons) =>
            val fieldSyms = c.fields.map(f => id2sym(f._1))
            val bindings: Map[Identifier, Term] = (cons.fields zip fieldSyms).map(p => p._1.id -> (p._2: Term)).toMap
            ConstructorDec(id2sym(c.sym), (fieldSyms zip cons.fields).map { case (s, vd) =>
              (s, sortOf(vd.tpe)(using bindings))
            }, Seq.empty)
        })
      }))
    }
  }

  override protected def declareFunction(tfd: TypedFunDef): SSymbol = {
    val fd = tfd.fd

    def signature(fd: FunDef): (SSymbol, Seq[SortedVar], Sort, Map[Identifier, Term]) = {
      var bindings = Map.empty[Identifier, Term]
      val params = fd.params.map { vd =>
        val s = id2sym(vd.id)
        val sv = SortedVar(s, sortOf(vd.tpe)(using bindings))
        bindings += vd.id -> s
        sv
      }
      (id2sym(fd.id), params, sortOf(fd.returnType)(using bindings), bindings)
    }

    def tparams(fd: FunDef): Seq[SSymbol] = fd.tparams.map(tpd => id2sym(tpd.id))

    functions.getB(fd.typed) match {
      case Some(s) => s
      case None =>
        functions += fd.typed -> id2sym(fd.id)

        val scc = transitiveCallees(fd.id).filter(id2 => transitivelyCalls(id2, fd.id))
        if (scc.size <= 1) {
          val (s, params, returnSort, bindings) = signature(fd)
          val body = toSMT(fd.fullBody)(using bindings)
          val tps = tparams(fd)

          emit((scc.isEmpty, tps.isEmpty) match {
            case (true, true) => DefineFun(SMTFunDef(s, params, returnSort, body))
            case (false, true) => DefineFunRec(SMTFunDef(s, params, returnSort, body))
            case (true, false) => DefineFunPar(tps, SMTFunDef(s, params, returnSort, body))
            case (false, false) => DefineFunRecPar(tps, SMTFunDef(s, params, returnSort, body))
          })
        } else {
          val fds = scc.toList.sortBy(_.globalId).map(getFunction)
          functions ++= fds.map(fd => fd.typed -> id2sym(fd.id))

          val (decs, bodies) = (for (fd <- fds) yield {
            val (s, params, returnSort, bindings) = signature(fd)
            val tps = tparams(fd)
            val dec = if (tps.isEmpty) Right(FunDec(s, params, returnSort)) else Left(FunDecPar(tps, s, params, returnSort))
            (dec, toSMT(fd.fullBody)(using bindings))
          }).unzip

          emit(if (decs.exists(_.isLeft)) {
            DefineFunsRecPar(decs, bodies)
          } else {
            DefineFunsRec(decs.collect { case Right(dec) => dec }, bodies)
          })
        }

        id2sym(fd.id)
    }
  }

  /** The sorted variables of the binder `vds`, which may refer to the previous ones, and the
    * bindings of the binder's body. */
  private def binders(vds: Seq[ValDef])(using bindings: Map[Identifier, Term]): (Seq[SortedVar], Map[Identifier, Term]) = {
    var current = bindings
    val svs = vds.map { vd =>
      val s = id2sym(vd.id)
      val sv = SortedVar(s, sortOf(vd.tpe)(using current))
      current += vd.id -> s
      sv
    }
    (svs, current)
  }

  override def printScript(expr: Expr): Unit = {
    val tparams = typeOps.typeParamsOf(expr)
    val term = toSMT(expr)(using Map.empty)

    val adts = adtManager.types
      .collect { case adt: ADTType => adt.getSort.definition }
      .toSeq.distinct.sortBy(_.id.globalId)

    for (sort <- adts; fd <- sort.invariant) {
      val Seq(vd) = fd.params
      val s = id2sym(vd.id)
      val adtSort = declareSort(ADTType(sort.id, fd.tparams.map(_.tp)))
      val pred = toSMT(fd.fullBody)(using Map(vd.id -> s))
      if (fd.tparams.isEmpty) emit(DatatypeInvariant(s, adtSort, pred))
      else emit(DatatypeInvariantPar(fd.tparams.map(tpd => id2sym(tpd.id)), s, adtSort, pred))
    }

    for (sort <- adts; fd <- sort.equality) {
      val Sort(SMTIdentifier(sortSym, _), _) = declareSort(ADTType(sort.id, sort.typeArgs)): @unchecked
      emit(DatatypeEquality(sortSym, declareFunction(fd.typed)))
    }

    emit(if (tparams.nonEmpty) AssertPar(tparams.map(tp => id2sym(tp.id)).toSeq, term) else Assert(term))
  }

  override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]): Term = e match {
    case v @ Variable(id, tp, _) =>
      bindings.get(id) orElse variables.getB(v).map(s => s: Term) getOrElse {
        val tps = typeOps.typeParamsOf(tp).toSeq
        val sort = sortOf(tp)(using Map.empty)
        val s = extraVars.cachedB(v) {
          val s = id2sym(id)
          emit(if (tps.nonEmpty) DeclareConstPar(tps.map(tp => id2sym(tp.id)), s, sort) else DeclareConst(s, sort))
          s
        }
        if (tps.nonEmpty) QualifiedIdentifier(SMTIdentifier(s), Some(sort))
        else QualifiedIdentifier(SMTIdentifier(s), None)
      }

    case Lambda(args, body) =>
      val (params, newBindings) = binders(args)
      SMTLambda(params, toSMT(body)(using newBindings))

    case Forall(args, body) =>
      val (params, newBindings) = binders(args)
      SMTForall(params.head, params.tail, toSMT(body)(using newBindings))

    case Not(Forall(args, body)) =>
      val (params, newBindings) = binders(args)
      val negated = body match {
        case Not(b) => b
        case b => Not(b)
      }
      Exists(params.head, params.tail, toSMT(negated)(using newBindings))

    case Choose(vd, pred) =>
      val (Seq(param), newBindings) = binders(Seq(vd)): @unchecked
      SMTChoose(param.name, param.sort, toSMT(pred)(using newBindings))

    case adt @ ADT(id, tps, es) if es.nonEmpty && tps.nonEmpty && {
      // the arguments don't determine the type of the constructor
      val tcons = getConstructor(id)
      val determined = tcons.fields.flatMap(vd => typeOps.typeParamsOf(vd.getType)).toSet
      !getSort(tcons.sort).typeArgs.forall(determined)
    } =>
      val tcons = adt.getConstructor
      val sort = declareSort(ADTType(tcons.sort.id, tps))
      val constructor = constructors.toB(ADTCons(tcons.id, tcons.sort.definition.typeArgs))
      FunctionApplication(QualifiedIdentifier(SMTIdentifier(constructor), Some(sort)), es.map(toSMT))

    case FiniteBag(elems, base) =>
      elems.map { case (k, v) => Bags.Singleton(toSMT(k), toSMT(v)) }.reduceLeftOption(Bags.Union(_, _))
        .getOrElse(Bags.EmptyBag(sortOf(base)))

    case Tuple(es) =>
      FunctionApplication(QualifiedIdentifier(sym("tuple")), es.map(toSMT))

    case TupleSelect(t, i) =>
      FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("tuple.select"), Seq(SNumeral(i - 1)))), Seq(toSMT(t)))

    case UnitLiteral() =>
      QualifiedIdentifier(sym("tuple.unit"))

    case IsConstructor(e, id) =>
      val cons = getConstructor(id)
      declareSort(ADTType(cons.sort, cons.getSort.typeArgs))
      val c = constructors.toB(ADTCons(cons.id, cons.getSort.typeArgs))
      FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("is"), Seq(c))), Seq(toSMT(e)))

    case BVLiteral(false, _, _) => keyword(super.toSMT(e), "unsigned")
    case IntToBV(_, false, _) => keyword(super.toSMT(e), "unsigned")
    case BVSignedToUnsigned(e) => keyword(toSMT(e), "unsigned")
    case BVUnsignedToSigned(e) => keyword(toSMT(e), "signed")
    case CharLiteral(_) => keyword(super.toSMT(e), "char")

    case _ => super.toSMT(e)
  }
}
