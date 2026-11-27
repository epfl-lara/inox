/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

import generated.{Semantics => S}

/** Inox's trees in the semantics of `proofs/semantics.md`, as the Scala evaluator generated from
  * it has them, and that evaluator with oracles for what the semantics leaves to quantifiers. */
object Embedding {
  import inox.trees._
  given PrinterOptions = PrinterOptions()

  def list[A](xs: Seq[A]): S.List[A] = xs.foldRight(S.Nil(): S.List[A])(S.Cons(_, _))

  def bitSet(bs: scala.collection.immutable.BitSet): BigInt = bs.foldLeft(BigInt(0))((acc, i) => acc.setBit(i - 1))

  def bits(bv: BVLiteral): BigInt = bitSet(bv.value)

  def chars(s: Seq[Int]): S.List[BigInt] = list(s.map(BigInt(_)))

  /** An Inox type in the semantics, if it is in its fragment. */
  def tpe(t: Type): Option[S.Type] = t match {
    case IntegerType() => Some(S.IntegerType())
    case BooleanType() => Some(S.BooleanType())
    case UnitType() => Some(S.UnitType())
    case CharType() => Some(S.CharType())
    case RealType() => Some(S.RealType())
    case StringType() => Some(S.StringType())
    case BVType(s, w) => Some(S.BVType(s, BigInt(w)))
    case FPType(e, s) => Some(S.FPType(BigInt(e), BigInt(s)))
    case RoundingMode => Some(S.RoundingModeType())
    case TypeParameter(id, _) => Some(S.TypeParameter(id))
    case TupleType(ts) => types(ts).map(S.TupleType(_))
    case SetType(b) => tpe(b).map(S.SetType(_))
    case BagType(b) => tpe(b).map(S.BagType(_))
    case MapType(f, t) => for (a <- tpe(f); b <- tpe(t)) yield S.MapType(a, b)
    case FunctionType(f, t) => for (a <- types(f); b <- tpe(t)) yield S.FunctionType(a, b)
    case ADTType(id, tps) => types(tps).map(S.ADTType(id, _))
    case RefinementType(vd, prop) => for (b <- tpe(vd.tpe); p <- expr(prop)) yield S.RefinementType(vd.id, b, p)
    case PropType() => Some(S.PropType())
    case PiType(ps, to) => for (a <- paramList(ps); b <- tpe(to)) yield S.PiType(a, b)
    case SigmaType(ps, to) => for (a <- paramList(ps); b <- tpe(to)) yield S.SigmaType(a, b)
    case _ => None
  }

  def types(ts: Seq[Type]): Option[S.List[S.Type]] = {
    val cs = ts.map(tpe)
    if (cs.forall(_.isDefined)) Some(list(cs.flatten)) else None
  }

  def paramList(vds: Seq[ValDef]): Option[S.List[S.Param]] = {
    val cs = vds.map(vd => tpe(vd.tpe).map(S.Param(vd.id, _)))
    if (cs.forall(_.isDefined)) Some(list(cs.flatten)) else None
  }

  /** An Inox expression in the semantics, if it is in its fragment. */
  def expr(e: Expr): Option[S.Expr] = {
    def all(es: Seq[Expr]): Option[S.List[S.Expr]] = {
      val cs = es.map(expr)
      if (cs.forall(_.isDefined)) Some(list(cs.flatten)) else None
    }
    def two(l: Expr, r: Expr)(f: (S.Expr, S.Expr) => S.Expr) = for (a <- expr(l); b <- expr(r)) yield f(a, b)
    def pairs(ps: Seq[(Expr, Expr)]): Option[S.List[S.ExprPair]] = {
      val cs = ps.map { case (k, v) => for (a <- expr(k); b <- expr(v)) yield S.ExprPair(a, b) }
      if (cs.forall(_.isDefined)) Some(list(cs.flatten)) else None
    }
    e match {
      case v: Variable => Some(S.Variable(v.id))
      case IntegerLiteral(i) => Some(S.IntegerLiteral(i))
      case BooleanLiteral(b) => Some(S.BooleanLiteral(b))
      case UnitLiteral() => Some(S.UnitLiteral())
      case CharLiteral(c) => Some(S.CharLiteral(BigInt(c.toInt)))
      case bv: BVLiteral => Some(S.BVLiteral(bv.signed, BigInt(bv.size), bits(bv)))
      case FPLiteral(ex, sig, bs) => Some(S.FPLiteral(BigInt(ex), BigInt(sig), bitSet(bs)))
      case RoundNearestTiesToEven => Some(S.RoundNearestTiesToEven())
      case RoundNearestTiesToAway => Some(S.RoundNearestTiesToAway())
      case RoundTowardPositive => Some(S.RoundTowardPositive())
      case RoundTowardNegative => Some(S.RoundTowardNegative())
      case RoundTowardZero => Some(S.RoundTowardZero())
      case FPEquals(a, b) => two(a, b)(S.FPEquals(_, _))
      case FPAdd(rm, a, b) => for (m <- expr(rm); x <- expr(a); y <- expr(b)) yield S.FPAdd(m, x, y)
      case FPSub(rm, a, b) => for (m <- expr(rm); x <- expr(a); y <- expr(b)) yield S.FPSub(m, x, y)
      case FPMul(rm, a, b) => for (m <- expr(rm); x <- expr(a); y <- expr(b)) yield S.FPMul(m, x, y)
      case FPDiv(rm, a, b) => for (m <- expr(rm); x <- expr(a); y <- expr(b)) yield S.FPDiv(m, x, y)
      case FPFMA(rm, a, b, c) => for (m <- expr(rm); x <- expr(a); y <- expr(b); z <- expr(c)) yield S.FPFMA(m, x, y, z)
      case FPUMinus(a) => expr(a).map(S.FPUMinus(_))
      case FPAbs(a) => expr(a).map(S.FPAbs(_))
      case FPMax(a, b) => two(a, b)(S.FPMax(_, _))
      case FPMin(a, b) => two(a, b)(S.FPMin(_, _))
      case FPRound(rm, a) => two(rm, a)(S.FPRound(_, _))
      case Sqrt(rm, a) => two(rm, a)(S.Sqrt(_, _))
      case FPCast(ex, sig, rm, a) => two(rm, a)(S.FPCast(BigInt(ex), BigInt(sig), _, _))
      case FPFromBinary(ex, sig, a) => expr(a).map(S.FPFromBinary(BigInt(ex), BigInt(sig), _))
      case FPToBV(w, sg, rm, a) => two(rm, a)(S.FPToBV(BigInt(w), sg, _, _))
      case FPToReal(a) => expr(a).map(S.FPToReal(_))
      case FPLessThan(a, b) => two(a, b)(S.FPLessThan(_, _))
      case FPGreaterThan(a, b) => two(a, b)(S.FPGreaterThan(_, _))
      case FPLessEquals(a, b) => two(a, b)(S.FPLessEquals(_, _))
      case FPGreaterEquals(a, b) => two(a, b)(S.FPGreaterEquals(_, _))
      case FPIsZero(a) => expr(a).map(S.FPIsZero(_))
      case FPIsInfinite(a) => expr(a).map(S.FPIsInfinite(_))
      case FPIsNaN(a) => expr(a).map(S.FPIsNaN(_))
      case FPIsNegative(a) => expr(a).map(S.FPIsNegative(_))
      case FPIsPositive(a) => expr(a).map(S.FPIsPositive(_))
      case FPIsNormal(a) => expr(a).map(S.FPIsNormal(_))
      case FPIsSubnormal(a) => expr(a).map(S.FPIsSubnormal(_))
      case FractionLiteral(n, d) => Some(S.FractionLiteral(n, d))
      case s: StringLiteral => Some(S.StringLiteral(chars(s.value)))
      // the values of type parameters are integers in the semantics
      case GenericValue(_, id) => Some(S.IntegerLiteral(BigInt(id)))
      case Lambda(params, body) => for (ps <- paramList(params); b <- expr(body)) yield S.Lambda(ps, b)
      case Forall(params, body) => for (ps <- paramList(params); b <- expr(body)) yield S.Forall(ps, b)
      case UninterpretedCall(id, tps, args, _) => for (ts <- types(tps); as <- all(args)) yield S.UninterpretedCall(id, ts, as)
      case Application(callee, args) => for (c <- expr(callee); as <- all(args)) yield S.Application(c, as)
      case Tuple(es) => all(es).map(S.Tuple(_))
      case TupleSelect(t, i) => expr(t).map(S.TupleSelect(_, BigInt(i)))
      case StringConcat(l, r) => two(l, r)(S.StringConcat(_, _))
      case SubString(a, b, c) => for (x <- expr(a); y <- expr(b); z <- expr(c)) yield S.SubString(x, y, z)
      case StringLength(a) => expr(a).map(S.StringLength(_))
      case BVNot(a) => expr(a).map(S.BVNot(_))
      case BVAnd(l, r) => two(l, r)(S.BVAnd(_, _))
      case BVOr(l, r) => two(l, r)(S.BVOr(_, _))
      case BVXor(l, r) => two(l, r)(S.BVXor(_, _))
      case BVShiftLeft(l, r) => two(l, r)(S.BVShiftLeft(_, _))
      case BVAShiftRight(l, r) => two(l, r)(S.BVAShiftRight(_, _))
      case BVLShiftRight(l, r) => two(l, r)(S.BVLShiftRight(_, _))
      case BVNarrowingCast(a, t) => expr(a).map(S.BVNarrowingCast(_, BigInt(t.size)))
      case BVWideningCast(a, t) => expr(a).map(S.BVWideningCast(_, BigInt(t.size)))
      case BVUnsignedToSigned(a) => expr(a).map(S.BVUnsignedToSigned(_))
      case BVSignedToUnsigned(a) => expr(a).map(S.BVSignedToUnsigned(_))
      case BVToInt(a) => expr(a).map(S.BVToInt(_))
      case IntToBV(size, signed, a) => expr(a).map(S.IntToBV(BigInt(size), signed, _))
      case FiniteSet(es, _) => all(es).map(S.FiniteSet(_))
      case SetAdd(a, b) => two(a, b)(S.SetAdd(_, _))
      case ElementOfSet(a, b) => two(a, b)(S.ElementOfSet(_, _))
      case SubsetOf(a, b) => two(a, b)(S.SubsetOf(_, _))
      case SetIntersection(a, b) => two(a, b)(S.SetIntersection(_, _))
      case SetUnion(a, b) => two(a, b)(S.SetUnion(_, _))
      case SetDifference(a, b) => two(a, b)(S.SetDifference(_, _))
      case FiniteBag(ps, _) => pairs(ps).map(S.FiniteBag(_))
      case BagAdd(a, b) => two(a, b)(S.BagAdd(_, _))
      case MultiplicityInBag(a, b) => two(a, b)(S.MultiplicityInBag(_, _))
      case BagIntersection(a, b) => two(a, b)(S.BagIntersection(_, _))
      case BagUnion(a, b) => two(a, b)(S.BagUnion(_, _))
      case BagDifference(a, b) => two(a, b)(S.BagDifference(_, _))
      case FiniteMap(ps, d, _, _) => for (xs <- pairs(ps); y <- expr(d)) yield S.FiniteMap(xs, y)
      case MapApply(a, b) => two(a, b)(S.MapApply(_, _))
      case MapUpdated(a, b, c) => for (x <- expr(a); y <- expr(b); z <- expr(c)) yield S.MapUpdated(x, y, z)
      case MapMerge(a, b, c) => for (x <- expr(a); y <- expr(b); z <- expr(c)) yield S.MapMerge(x, y, z)
      case Let(vd, v, b) => two(v, b)(S.Let(vd.id, _, _))
      case IfExpr(c, t, f) => for (a <- expr(c); b <- expr(t); d <- expr(f)) yield S.IfExpr(a, b, d)
      case Assume(p, b) => two(p, b)(S.Assume(_, _))
      case Error(_, _) => Some(S.Error())
      case FunctionInvocation(id, tps, args) => for (ts <- types(tps); as <- all(args)) yield S.FunctionInvocation(id, ts, as)
      case ADT(id, tps, args) => for (ts <- types(tps); as <- all(args)) yield S.ADT(id, ts, as)
      case IsConstructor(a, id) => expr(a).map(S.IsConstructor(_, id))
      case ADTSelector(a, id) => expr(a).map(S.ADTSelector(_, id))
      case Equals(l, r) => two(l, r)(S.Equals(_, _))
      case And(es) => all(es).map(S.And(_))
      case Or(es) => all(es).map(S.Or(_))
      case Implies(l, r) => two(l, r)(S.Implies(_, _))
      case Not(a) => expr(a).map(S.Not(_))
      case Plus(l, r) => two(l, r)(S.Plus(_, _))
      case Minus(l, r) => two(l, r)(S.Minus(_, _))
      case UMinus(a) => expr(a).map(S.UMinus(_))
      case Times(l, r) => two(l, r)(S.Times(_, _))
      case Division(l, r) => two(l, r)(S.Division(_, _))
      case Remainder(l, r) => two(l, r)(S.Remainder(_, _))
      case Modulo(l, r) => two(l, r)(S.Modulo(_, _))
      case LessThan(l, r) => two(l, r)(S.LessThan(_, _))
      case GreaterThan(l, r) => two(l, r)(S.GreaterThan(_, _))
      case LessEquals(l, r) => two(l, r)(S.LessEquals(_, _))
      case GreaterEquals(l, r) => two(l, r)(S.GreaterEquals(_, _))
      case _ => None
    }
  }

  /** Whether the semantics covers the types of `e`'s subexpressions. */
  def inFragment(e: Expr)(using Symbols): Boolean = exprOps.collect[Type] {
    case e => Set(e.getType)
  }(e).forall(supported) &&
    // the uninterpreted functions of the regression files have no model to give them
    !exprOps.exists { case _: UninterpretedCall => true; case _ => false }(e)

  def supported(t: Type): Boolean = t match {
    case IntegerType() | BooleanType() | UnitType() | CharType() | RealType() | StringType() |
         _: BVType | _: FPType | RoundingMode | _: TypeParameter => true
    case ADTType(_, tps) => tps.forall(supported)
    case TupleType(ts) => ts.forall(supported)
    case FunctionType(from, to) => (from :+ to).forall(supported)
    case PropType() => true
    case PiType(ps, to) => (ps.map(_.tpe) :+ to).forall(supported)
    case SigmaType(ps, to) => (ps.map(_.tpe) :+ to).forall(supported)
    case SetType(b) => supported(b)
    case BagType(b) => supported(b)
    case MapType(f, t) => supported(f) && supported(t)
    case _ => false
  }

  /** The functions of `symbols` in the fragment, with the functions they call. */
  def coveredFunctions(using symbols: Symbols): Map[Identifier, S.FunDef] = {
    val candidates = symbols.functions.values.flatMap { fd =>
      if (!inFragment(fd.fullBody) || !(fd.params.map(_.tpe) :+ fd.returnType).forall(supported)) None
      else expr(fd.fullBody).map(b => fd.id -> S.FunDef(fd.id, list(fd.tparams.map(_.id)), list(fd.params.map(_.id)), b))
    }.toMap
    var covered = candidates
    var changed = true
    while (changed) {
      val next = covered.filter { case (id, _) => symbols.getFunction(id).fullBody match {
        case body => exprOps.functionCallsOf(body).forall(fi => covered.contains(fi.id)) &&
          // the invariants of the sorts that the body builds
          exprOps.collect[Identifier] { case ADT(c, _, _) => symbols.getConstructor(c).getSort.invariant.map(_.id).toSet
                                       case _ => Set() }(body).forall(covered.contains)
      }}
      changed = next.size != covered.size
      covered = next
    }
    covered
  }

  def program(functions: Map[Identifier, S.FunDef])(using symbols: Symbols): S.Program = S.Program(
    list(functions.values.toSeq),
    // the types of fields only matter to quantifiers, which these tests enumerate on finite types
    list(symbols.constructors.values.toSeq.map(c => S.Constructor(c.id, c.sort,
      list(c.fields.map(vd => S.Param(vd.id, tpe(vd.tpe).getOrElse(S.UnitType()))))))),
    list(symbols.sorts.values.toSeq.map(s => S.Sort(s.id, list(s.tparams.map(_.id)), s.invariant.map(_.id) match {
      case scala.Some(id) => S.Some(id)
      case scala.None => S.None()
    }))),
    S.Nil(),
    S.NoFunctionEquality())

  final class Unsupported extends Exception

  /** The generated evaluator, with oracles for the functions that quantify: here, quantifiers are
    * enumerated over small finite types only, predicates are evaluated with `fuel`, and the
    * types of functions aren't checked. */
  class Evaluator(fuel: BigInt) extends S.Evaluator {
    private def product(ds: Seq[Seq[S.Value]]): Seq[Seq[S.Value]] =
      ds.foldRight(Seq(Seq.empty[S.Value]))((d, rest) => for (v <- d; vs <- rest) yield v +: vs)
    /** Values that include those of `t`, which `has-type` then filters. */
    private def domain(t: S.Type): Seq[S.Value] = t match {
      case S.BooleanType() | S.PropType() => Seq(S.BoolV(false), S.BoolV(true))
      case S.TupleType(ts) => product(toSeq(ts).map(domain)).map(vs => S.TupleV(list(vs)))
      case S.SigmaType(ps, to) =>
        product(toSeq(ps).map { case S.Param(_, t) => domain(t) } :+ domain(to)).map(vs => S.TupleV(list(vs)))
      case S.RefinementType(_, b, _) => domain(b)
      case S.UnitType() => Seq(S.UnitV())
      case S.BVType(s, w) if w <= 4 => (BigInt(0) until BigInt(2).pow(w.toInt)).map(S.BVV(s, w, _))
      case _ => throw Unsupported()
    }
    private def toSeq[A](l: S.List[A]): Seq[A] = l match {
      case S.Nil() => Seq()
      case S.Cons(h, t) => h +: toSeq(t)
    }
    def forall_result(P: S.Program, fuel: BigInt, env: S.Env, params: S.List[S.Param], body: S.Expr): S.Result[S.Value] = {
      val inputs = product(toSeq(params).map { case S.Param(_, t) => domain(t) })
        .filter(vs => params_have_types(P, env, list(vs), params))
      val results = inputs.map(vs => instance(P, fuel, env, params, list(vs), body))
      if (results.contains(S.Ok(S.BoolV(false)))) S.Ok(S.BoolV(false))
      else if (results.contains(S.OutOfFuel())) S.OutOfFuel()
      else if (results.forall(_ == S.Ok(S.BoolV(true)))) S.Ok(S.BoolV(true))
      else S.Stuck()
    }
    def holds(P: S.Program, env: S.Env, prop: S.Expr): Boolean = eval(P, fuel, env, prop) == S.Ok(S.BoolV(true))
    def invariant_holds(P: S.Program, f: Identifier, args: S.List[S.Type], tenv: S.List[S.TypeBinding], v: S.Value): Boolean =
      call(P, fuel, f, args, tenv, S.Cons(v, S.Nil())) == S.Ok(S.BoolV(true))
    def function_has_type(P: S.Program, env: S.Env, f: S.Value, from: S.List[S.Type], to: S.Type): Boolean = throw Unsupported()
    def pi_has_type(P: S.Program, env: S.Env, f: S.Value, ps: S.List[S.Param], to: S.Type): Boolean = throw Unsupported()
    def closures_equal(P: S.Program, f: S.Value, g: S.Value): Boolean = throw Unsupported()
  }

  /** A value of Inox's evaluator in the semantics, or `None` for one that contains a function,
    * which the two evaluators represent differently. */
  def value(e: Expr): scala.Option[S.Value] = {
    def all(es: Seq[Expr]) = {
      val vs = es.map(value)
      if (vs.forall(_.isDefined)) scala.Some(list(vs.flatten)) else scala.None
    }
    e match {
      case IntegerLiteral(i) => scala.Some(S.IntV(i))
      case BooleanLiteral(b) => scala.Some(S.BoolV(b))
      case UnitLiteral() => scala.Some(S.UnitV())
      case CharLiteral(c) => scala.Some(S.CharV(BigInt(c.toInt)))
      case FractionLiteral(n, d) =>
        val g = n.gcd(d) * d.signum
        scala.Some(S.RealV(n / g, d / g))
      case s: StringLiteral => scala.Some(S.StringV(chars(s.value)))
      case bv: BVLiteral => scala.Some(S.BVV(bv.signed, BigInt(bv.size), bits(bv)))
      case FPLiteral(ex, sig, bs) => scala.Some(S.FPV(BigInt(ex), BigInt(sig), bitSet(bs)))
      case GenericValue(_, id) => scala.Some(S.IntV(BigInt(id)))
      case Tuple(es) => all(es).map(S.TupleV(_))
      case ADT(id, _, args) => all(args).map(S.ADTV(id, _))
      case FiniteSet(es, _) => all(es).map(S.SetV(_))
      case FiniteBag(ps, _) =>
        val es = ps.map { case (k, IntegerLiteral(n)) => value(k).map(S.BagEntry(_, n)); case _ => scala.None }
        if (es.forall(_.isDefined)) scala.Some(S.BagV(list(es.flatten))) else scala.None
      case FiniteMap(ps, d, _, _) =>
        val es = ps.map { case (k, v) => for (a <- value(k); b <- value(v)) yield S.MapEntry(a, b) }
        if (es.forall(_.isDefined)) value(d).map(S.MapV(list(es.flatten), _)) else scala.None
      case _: Lambda => scala.None
      case _ => throw new IllegalArgumentException(s"not a value of the semantics: $e")
    }
  }
}
