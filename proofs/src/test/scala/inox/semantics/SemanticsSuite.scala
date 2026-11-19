/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

import java.nio.file.{Files, Paths}

import org.scalatest.funsuite.AnyFunSuite

import generated.{Semantics => S}

/** The semantics of `proofs/semantics.md`, as the Scala evaluator generated from it, against
  * [[evaluators.RecursiveEvaluator]], and the generated evaluator against the file. */
class SemanticsSuite extends AnyFunSuite {
  import inox.trees._
  given PrinterOptions = PrinterOptions()

  private def list[A](xs: Seq[A]): S.List[A] = xs.foldRight(S.Nil(): S.List[A])(S.Cons(_, _))

  private def bits(bv: BVLiteral): BigInt = bv.value.foldLeft(BigInt(0))((acc, i) => acc.setBit(i - 1))

  private def chars(s: Seq[Int]): S.List[BigInt] = list(s.map(BigInt(_)))

  /** An Inox type in the semantics, if it is in its fragment. */
  def tpe(t: Type): Option[S.Type] = t match {
    case IntegerType() => Some(S.IntegerType())
    case BooleanType() => Some(S.BooleanType())
    case UnitType() => Some(S.UnitType())
    case CharType() => Some(S.CharType())
    case RealType() => Some(S.RealType())
    case StringType() => Some(S.StringType())
    case BVType(s, w) => Some(S.BVType(s, BigInt(w)))
    case TypeParameter(id, _) => Some(S.TypeParameter(id))
    case TupleType(ts) => types(ts).map(S.TupleType(_))
    case SetType(b) => tpe(b).map(S.SetType(_))
    case BagType(b) => tpe(b).map(S.BagType(_))
    case MapType(f, t) => for (a <- tpe(f); b <- tpe(t)) yield S.MapType(a, b)
    case FunctionType(f, t) => for (a <- types(f); b <- tpe(t)) yield S.FunctionType(a, b)
    case ADTType(id, tps) => types(tps).map(S.ADTType(id, _))
    case RefinementType(vd, prop) => for (b <- tpe(vd.tpe); p <- expr(prop)) yield S.RefinementType(vd.id, b, p)
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
         _: BVType | _: TypeParameter => true
    case ADTType(_, tps) => tps.forall(supported)
    case TupleType(ts) => ts.forall(supported)
    case FunctionType(from, to) => (from :+ to).forall(supported)
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
    * enumerated over small finite types only. */
  object Sem extends S.Evaluator {
    private def domain(t: S.Type): Seq[S.Value] = t match {
      case S.BooleanType() => Seq(S.BoolV(false), S.BoolV(true))
      case S.UnitType() => Seq(S.UnitV())
      case S.BVType(s, w) if w <= 4 => (BigInt(0) until BigInt(2).pow(w.toInt)).map(S.BVV(s, w, _))
      case _ => throw Unsupported()
    }
    private def toSeq[A](l: S.List[A]): Seq[A] = l match {
      case S.Nil() => Seq()
      case S.Cons(h, t) => h +: toSeq(t)
    }
    def forall_result(P: S.Program, fuel: BigInt, env: S.Env, params: S.List[S.Param], body: S.Expr): S.Result[S.Value] = {
      val domains = toSeq(params).map { case S.Param(_, t) => domain(t) }
      val inputs = domains.foldRight(Seq(Seq.empty[S.Value]))((d, rest) => for (v <- d; vs <- rest) yield v +: vs)
      val results = inputs.map(vs => instance(P, fuel, env, params, list(vs), body))
      if (results.contains(S.Ok(S.BoolV(false)))) S.Ok(S.BoolV(false))
      else if (results.contains(S.OutOfFuel())) S.OutOfFuel()
      else if (results.forall(_ == S.Ok(S.BoolV(true)))) S.Ok(S.BoolV(true))
      else S.Stuck()
    }
    def has_type(P: S.Program, tenv: S.List[S.TypeBinding], v: S.Value, t: S.Type): Boolean = throw Unsupported()
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
      case _ => fail(s"not a value of the semantics: $e")
    }
  }

  val fuel = BigInt(40)
  val maxCalls = 20000

  enum Outcome {
    case Value, Stuck, Skipped
  }

  /** Evaluates `e` (closed, in the fragment) with both evaluators, and fails if they disagree. */
  def compare(e: Expr, sp: S.Program, label: => String)(using symbols: Symbols): Outcome = {
    val ctx = TestContext(Options(Seq(evaluators.optMaxCalls(maxCalls))))
    val ev = evaluators.RecursiveEvaluator(InoxProgram(symbols), ctx)
    val reference = try ev.eval(e) catch {
      case _: StackOverflowError => return Outcome.Skipped
    }
    val ours = try Sem.eval(sp, fuel, S.Env(S.Nil(), S.Nil()), expr(e).get) catch {
      case _: Unsupported => return Outcome.Skipped
    }
    (reference, ours) match {
      case (_, S.OutOfFuel()) => Outcome.Skipped
      case (evaluators.EvaluationResults.RuntimeError(msg), _) if msg.startsWith("Exceeded") => Outcome.Skipped
      case (evaluators.EvaluationResults.Successful(v), S.Ok(w)) =>
        // collections are compared by their contents
        value(v).foreach(v => assert(Sem.value_eq(sp, v, w) == S.Ok(true), s"$label: ${e.asString} gives ${v} and ${w} in the semantics"))
        Outcome.Value
      case (evaluators.EvaluationResults.RuntimeError(_), S.Stuck()) => Outcome.Stuck
      case (r, o) => fail(s"$label: ${e.asString} gives $r and $o in the semantics")
    }
  }

  /** Small values of type `t`, of ADT depth at most `depth`. */
  def values(t: Type, depth: Int, rnd: scala.util.Random)(using symbols: Symbols): scala.Option[Expr] = t match {
    case _ if depth < -3 => scala.None
    case IntegerType() => scala.Some(IntegerLiteral(Seq(-17, -3, -2, -1, 0, 1, 2, 3, 5, 100)(rnd.nextInt(10))))
    case BooleanType() => scala.Some(BooleanLiteral(rnd.nextBoolean()))
    case UnitType() => scala.Some(UnitLiteral())
    case CharType() => scala.Some(CharLiteral("aZ0 é\u0000"(rnd.nextInt(6))))
    case RealType() =>
      scala.Some(FractionLiteral(BigInt(rnd.nextInt(21) - 10), BigInt(rnd.nextInt(4) + 1)))
    case StringType() =>
      scala.Some(StringLiteral(Seq.fill(rnd.nextInt(4))("ab "(rnd.nextInt(3)).toInt)))
    case BVType(signed, size) => scala.Some(bvValue(signed, size, rnd))
    case TupleType(ts) =>
      val vs = ts.map(values(_, depth - 1, rnd))
      if (vs.forall(_.isDefined)) scala.Some(Tuple(vs.flatten)) else scala.None
    case SetType(b) =>
      val vs = Seq.fill(rnd.nextInt(4))(values(b, depth - 1, rnd))
      if (vs.forall(_.isDefined)) scala.Some(FiniteSet(vs.flatten, b)) else scala.None
    case BagType(b) =>
      val vs = Seq.fill(rnd.nextInt(4))(values(b, depth - 1, rnd))
      if (vs.forall(_.isDefined)) scala.Some(FiniteBag(vs.flatten.map(_ -> IntegerLiteral(rnd.nextInt(3) + 1)), b))
      else scala.None
    case MapType(f, t) =>
      val ps = Seq.fill(rnd.nextInt(4))((values(f, depth - 1, rnd), values(t, depth - 1, rnd)))
      val d = values(t, depth - 1, rnd)
      if (d.isDefined && ps.forall((a, b) => a.isDefined && b.isDefined))
        scala.Some(FiniteMap(ps.map((a, b) => a.get -> b.get), d.get, f, t))
      else scala.None
    case FunctionType(from, to) =>
      // a constant function
      values(to, depth - 1, rnd).map(v => Lambda(from.map(t => ValDef.fresh("x", t)), v))
    case adt: ADTType =>
      val sort = adt.getSort
      val ctors = sort.constructors
      val leaves = ctors.filter(_.fields.forall(f => !f.tpe.isInstanceOf[ADTType] || f.tpe != adt))
      val pool = if (depth <= 0 && leaves.nonEmpty) leaves else ctors
      val c = pool(rnd.nextInt(pool.size))
      val args = c.fields.map(f => values(f.tpe, depth - 1, rnd))
      if (args.forall(_.isDefined) && depth > -3) scala.Some(ADT(c.id, adt.tps, args.flatten)) else scala.None
    case _ => scala.None
  }

  /** A bit-vector, often at the edges of its range. */
  def bvValue(signed: Boolean, size: Int, rnd: scala.util.Random): Expr = {
    val (lo, hi) = if (signed) (-BigInt(2).pow(size - 1), BigInt(2).pow(size - 1) - 1) else (BigInt(0), BigInt(2).pow(size) - 1)
    val v = rnd.nextInt(8) match {
      case 0 => lo
      case 1 => hi
      case 2 => BigInt(0)
      case 3 => if (signed) BigInt(-1) else BigInt(1)
      case 4 => BigInt(rnd.nextInt(2 * size + 1))
      case _ => lo + (BigInt(size + 8, rnd) mod (hi - lo + 1))
    }
    BVLiteral(signed, v, size)
  }

  test("The generated evaluator is up to date with proofs/semantics.md") {
    val generated = Codegen.scala(Paths.get(Codegen.source))
    assert(generated == Files.readString(Paths.get(Codegen.scalaOutput)),
      "run `sbt proofs/run` to regenerate it")
  }

  test("Integer division and remainders are euclidean, and stuck on zero") {
    given Symbols = NoSymbols
    val sp = program(Map())
    def run(e: Expr) = Sem.eval(sp, fuel, S.Env(S.Nil(), S.Nil()), expr(e).get)
    for ((a, b, q, r) <- Seq((7, 2, 3, 1), (-7, 2, -4, 1), (7, -2, -3, 1), (-7, -2, 4, 1))) {
      val (x, y) = (IntegerLiteral(a), IntegerLiteral(b))
      assert(run(Division(x, y)) == S.Ok(S.IntV(q)))
      assert(run(Remainder(x, y)) == S.Ok(S.IntV(r)))
      assert(run(Modulo(x, y)) == S.Ok(S.IntV(r)))
      for (e <- Seq(Division(x, y), Remainder(x, y), Modulo(x, y)))
        assert(compare(e, sp, "division") == Outcome.Value)
    }
    for (e <- Seq(Division(IntegerLiteral(1), IntegerLiteral(0)), Modulo(IntegerLiteral(1), IntegerLiteral(0)))) {
      assert(run(e) == S.Stuck())
      assert(compare(e, sp, "division by zero") == Outcome.Stuck)
    }
  }

  /** Compares the two evaluators on `count` random instances of each of `ops`, and checks that each
    * op both succeeds and gets stuck (if `stuck`) at least once. */
  def compareOps(label: String, ops: Seq[(String, scala.util.Random => Expr)], count: Int): Unit = {
    given Symbols = NoSymbols
    val sp = program(Map())
    val rnd = new scala.util.Random(1)
    for ((name, op) <- ops) {
      val outcomes = (1 to count).map(_ => compare(op(rnd), sp, s"$label $name"))
      assert(outcomes.contains(Outcome.Value), s"$label $name never gives a value")
    }
  }

  test("Bit-vector arithmetic, bitwise operations and casts") {
    val shapes = Seq((true, 8), (false, 8), (true, 32), (false, 32), (true, 1), (false, 3))
    def two(f: (Expr, Expr) => Expr) = (rnd: scala.util.Random) => {
      val (s, w) = shapes(rnd.nextInt(shapes.size))
      f(bvValue(s, w, rnd), bvValue(s, w, rnd))
    }
    def one(f: Expr => Expr) = (rnd: scala.util.Random) => {
      val (s, w) = shapes(rnd.nextInt(shapes.size))
      f(bvValue(s, w, rnd))
    }
    def cast(rnd: scala.util.Random) = {
      val (s, w) = shapes(rnd.nextInt(shapes.size))
      val v = bvValue(s, w, rnd)
      val to = Seq(1, 3, 8, 16, 32, 64)(rnd.nextInt(6))
      if (to < w) BVNarrowingCast(v, BVType(s, to)) else if (to > w) BVWideningCast(v, BVType(s, to)) else v
    }
    compareOps("bit-vector", Seq(
      "+" -> two(Plus(_, _)), "-" -> two(Minus(_, _)), "*" -> two(Times(_, _)),
      "/" -> two(Division(_, _)), "rem" -> two(Remainder(_, _)), "mod" -> two(Modulo(_, _)),
      "<" -> two(LessThan(_, _)), ">" -> two(GreaterThan(_, _)),
      "<=" -> two(LessEquals(_, _)), ">=" -> two(GreaterEquals(_, _)), "==" -> two(Equals(_, _)),
      "&" -> two(BVAnd(_, _)), "|" -> two(BVOr(_, _)), "^" -> two(BVXor(_, _)),
      "<<" -> two(BVShiftLeft(_, _)), ">>" -> two(BVAShiftRight(_, _)), ">>>" -> two(BVLShiftRight(_, _)),
      "~" -> one(BVNot(_)), "neg" -> one(UMinus(_)), "toInt" -> one(BVToInt(_)), "cast" -> cast,
      "toSigned" -> one(e => if (e.asInstanceOf[BVLiteral].signed) BVSignedToUnsigned(e) else BVUnsignedToSigned(e)),
      "fromInt" -> ((rnd: scala.util.Random) =>
        IntToBV(Seq(1, 8, 32)(rnd.nextInt(3)), rnd.nextBoolean(), IntegerLiteral(BigInt(40, rnd) - BigInt(2).pow(39))))
    ), 300)
  }

  test("Reals, characters, strings, tuples and functions") {
    def real(rnd: scala.util.Random): Expr =
      FractionLiteral(BigInt(rnd.nextInt(21) - 10), BigInt(rnd.nextInt(7) - 3) match { case d if d == 0 => BigInt(1); case d => d })
    def str(rnd: scala.util.Random): Expr = StringLiteral(Seq.fill(rnd.nextInt(5))("abc"(rnd.nextInt(3)).toInt))
    def int(rnd: scala.util.Random): Expr = IntegerLiteral(rnd.nextInt(9) - 2)
    def chr(rnd: scala.util.Random): Expr = CharLiteral("ab"(rnd.nextInt(2)))
    val x = ValDef.fresh("x", IntegerType())
    val y = ValDef.fresh("y", IntegerType())
    val tp = TypeParameter.fresh("T")
    val f = ValDef.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    compareOps("theories", Seq(
      "real +" -> (r => Plus(real(r), real(r))), "real -" -> (r => Minus(real(r), real(r))),
      "real *" -> (r => Times(real(r), real(r))), "real /" -> (r => Division(real(r), real(r))),
      "real neg" -> (r => UMinus(real(r))), "real <" -> (r => LessThan(real(r), real(r))),
      "real <=" -> (r => LessEquals(real(r), real(r))), "real ==" -> (r => Equals(real(r), real(r))),
      "char <" -> (r => LessThan(chr(r), chr(r))), "char ==" -> (r => Equals(chr(r), chr(r))),
      "concat" -> (r => StringConcat(str(r), str(r))), "length" -> (r => StringLength(str(r))),
      "substring" -> (r => SubString(str(r), int(r), int(r))), "string ==" -> (r => Equals(str(r), str(r))),
      "tuple" -> (r => TupleSelect(Tuple(Seq(int(r), str(r), real(r))), r.nextInt(3) + 1)),
      "tuple ==" -> (r => Equals(Tuple(Seq(int(r), chr(r))), Tuple(Seq(int(r), chr(r))))),
      // a closure captures its environment, and applying it evaluates its body there
      "apply" -> (r => Let(x, int(r), Application(Lambda(Seq(y),
        Plus(x.toVariable, y.toVariable)), Seq(int(r))))),
      "higher order" -> (r => Let(f, Lambda(Seq(x), Times(x.toVariable, int(r))),
        Application(f.toVariable, Seq(Application(f.toVariable, Seq(int(r))))))),
      "lambda" -> (r => Lambda(Seq(x), Plus(x.toVariable, int(r)))),
      "generic" -> (r => Equals(GenericValue(tp, r.nextInt(2)), GenericValue(tp, r.nextInt(2))))
    ), 100)
  }

  test("Sets, bags and maps") {
    def int(rnd: scala.util.Random): Expr = IntegerLiteral(rnd.nextInt(4))
    def set(rnd: scala.util.Random): Expr = FiniteSet(Seq.fill(rnd.nextInt(4))(int(rnd)), IntegerType())
    def bag(rnd: scala.util.Random): Expr =
      FiniteBag(Seq.fill(rnd.nextInt(4))(int(rnd) -> IntegerLiteral(rnd.nextInt(5) - 1)), IntegerType())
    def map(rnd: scala.util.Random): Expr =
      FiniteMap(Seq.fill(rnd.nextInt(4))(int(rnd) -> int(rnd)), int(rnd), IntegerType(), IntegerType())
    val f = Lambda(Seq(ValDef.fresh("x", IntegerType())), IntegerLiteral(0))
    compareOps("collections", Seq(
      "set" -> set, "set ==" -> (r => Equals(set(r), set(r))), "add" -> (r => SetAdd(set(r), int(r))),
      "in" -> (r => ElementOfSet(int(r), set(r))), "subset" -> (r => SubsetOf(set(r), set(r))),
      "inter" -> (r => SetIntersection(set(r), set(r))), "union" -> (r => SetUnion(set(r), set(r))),
      "diff" -> (r => SetDifference(set(r), set(r))),
      "bag" -> bag, "bag ==" -> (r => Equals(bag(r), bag(r))), "bag add" -> (r => BagAdd(bag(r), int(r))),
      "multiplicity" -> (r => MultiplicityInBag(int(r), bag(r))),
      "bag inter" -> (r => BagIntersection(bag(r), bag(r))), "bag union" -> (r => BagUnion(bag(r), bag(r))),
      "bag diff" -> (r => BagDifference(bag(r), bag(r))),
      "map" -> map, "map ==" -> (r => Equals(map(r), map(r))), "apply" -> (r => MapApply(map(r), int(r))),
      "updated" -> (r => MapUpdated(map(r), int(r), int(r))),
      "merge" -> (r => MapMerge(set(r), map(r), map(r))),
      // maps whose values are functions can be built and read, but not compared
      "function map" -> (r => MapApply(FiniteMap(Seq(int(r) -> f), f, IntegerType(), f.getType(using NoSymbols)), int(r))),
      "nested ==" -> (r => Equals(FiniteSet(Seq(set(r), set(r)), SetType(IntegerType())),
                                  FiniteSet(Seq(set(r), set(r)), SetType(IntegerType()))))
    ), 200)
  }

  test("Quantifiers: a false instance wins, then running out of fuel, then getting stuck") {
    given Symbols = NoSymbols
    val sp = program(Map())
    def run(e: Expr) = Sem.eval(sp, fuel, S.Env(S.Nil(), S.Nil()), expr(e).get)
    val b = ValDef.fresh("b", BooleanType())
    val x = ValDef.fresh("x", BVType(true, 3))
    val v = b.toVariable
    assert(run(Forall(Seq(b), Or(v, Not(v)))) == S.Ok(S.BoolV(true)))
    assert(run(Forall(Seq(b), v)) == S.Ok(S.BoolV(false)))
    // stuck for `b = true`, false for `b = false`
    assert(run(Forall(Seq(b), IfExpr(v, Error(BooleanType(), "e"), BooleanLiteral(false)))) == S.Ok(S.BoolV(false)))
    assert(run(Forall(Seq(b), IfExpr(v, Error(BooleanType(), "e"), BooleanLiteral(true)))) == S.Stuck())
    assert(run(Forall(Seq(x), LessEquals(x.toVariable, BVLiteral(true, 3, 3)))) == S.Ok(S.BoolV(true)))
    assert(run(Forall(Seq(x), LessThan(x.toVariable, BVLiteral(true, 3, 3)))) == S.Ok(S.BoolV(false)))
    for (e <- Seq(Forall(Seq(b), Or(v, Not(v))), Forall(Seq(b), v),
                  Forall(Seq(x, b), Implies(v, LessEquals(x.toVariable, BVLiteral(true, 3, 3))))))
      assert(compare(e, sp, "forall") == Outcome.Value)
  }

  test("Assumptions, errors, invariants, selectors and fuel") {
    import dsl._
    val (listId, nilId, consId) = (FreshIdentifier("List"), FreshIdentifier("Nil"), FreshIdentifier("Cons"))
    val (headId, tailId) = (FreshIdentifier("head"), FreshIdentifier("tail"))
    val List = mkSort(listId)() { _ => Seq(
      (nilId, Seq()),
      (consId, Seq(ValDef(headId, IntegerType()), ValDef(tailId, T(listId)()))))
    }
    val sizeId = FreshIdentifier("size")
    val size = mkFunDef(sizeId)() { _ =>
      (Seq("l" :: T(listId)()), IntegerType(), { case Seq(l) =>
        if_ (l.is(consId)) { E(BigInt(1)) + E(sizeId)(l.getField(tailId)) } else_ { E(BigInt(0)) }
      })
    }
    val loopId = FreshIdentifier("loop")
    val loop = mkFunDef(loopId)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => E(loopId)(x) }) }
    given symbols: Symbols = NoSymbols.withSorts(Seq(List)).withFunctions(Seq(size, loop))
    val sp = program(coveredFunctions)
    def cons(h: Int, t: Expr) = ADT(consId, Seq(), Seq(IntegerLiteral(h), t))
    val nil = ADT(nilId, Seq(), Seq())
    def run(e: Expr) = Sem.eval(sp, fuel, S.Env(S.Nil(), S.Nil()), expr(e).get)

    assert(run(E(sizeId)(cons(1, cons(2, nil)))) == S.Ok(S.IntV(2)))
    assert(run(ADTSelector(nil, headId)) == S.Stuck())
    assert(run(Assume(BooleanLiteral(false), IntegerLiteral(1))) == S.Stuck())
    assert(run(Error(IntegerType(), "e")) == S.Stuck())
    assert(run(E(loopId)(IntegerLiteral(0))) == S.OutOfFuel())
    // `false && error` doesn't evaluate the error
    assert(run(And(BooleanLiteral(false), Error(BooleanType(), "e"))) == S.Ok(S.BoolV(false)))
    for (e <- Seq(E(sizeId)(cons(1, cons(2, nil))), ADTSelector(nil, headId), IsConstructor(nil, consId),
                  Assume(BooleanLiteral(false), IntegerLiteral(1)), Error(IntegerType(), "e"),
                  And(BooleanLiteral(false), Error(BooleanType(), "e")),
                  Equals(cons(1, nil), cons(1, nil)), Equals(cons(1, nil), nil)))
      assert(compare(e, sp, "unit") != Outcome.Skipped)
  }

  test("The semantics agrees with RecursiveEvaluator on the functions of the regression files") {
    val root = Paths.get("../src/it/resources/regression")
    val files = scala.jdk.CollectionConverters.ListHasAsScala(
      Files.walk(root).sorted().toList).asScala.toSeq.filter { f =>
        val n = f.toString
        (n.endsWith(".tip") && !n.contains("PARSING")) || n.endsWith(".smt3")
      }
    assert(files.nonEmpty, s"no regression files under $root")
    val rnd = new scala.util.Random(0)
    var valueCount = 0
    var stuck = 0
    var skipped = 0
    var testedFunctions = 0
    for (file <- files) {
      val parsed = try {
        if (file.toString.endsWith(".tip")) tip.Parser(file.toFile).parseScript
        else smtlib3.Parser(file.toFile).parseScript
      } catch { case _: Throwable => Seq() }
      for ((p, _) <- parsed.take(1)) {
        given symbols: Symbols = p.symbols.asInstanceOf[Symbols]
        val covered = coveredFunctions
        val sp = program(covered)
        for (id <- covered.keys.toSeq.sortBy(_.uniqueName)) {
          // type parameters range over the integers here: evaluation doesn't depend on them
          val tps = symbols.getFunction(id).tparams.map(_ => IntegerType())
          val tfd = symbols.getFunction(id, tps)
          testedFunctions += 1
          for (_ <- 1 to (if (tfd.params.isEmpty) 1 else 30)) {
            val args = tfd.params.map(vd => values(vd.tpe, 3, rnd))
            // the invariants of the arguments' sorts must be in the fragment
            val invariants = args.flatten.flatMap(exprOps.collect[Identifier] {
              case ADT(c, _, _) => symbols.getConstructor(c).getSort.invariant.map(_.id).toSet
              case _ => Set()
            })
            if (args.forall(_.isDefined) && invariants.forall(covered.contains)) {
              compare(FunctionInvocation(id, tps, args.flatten), sp, file.getFileName.toString) match {
                case Outcome.Value => valueCount += 1
                case Outcome.Stuck => stuck += 1
                case Outcome.Skipped => skipped += 1
              }
            }
          }
        }
      }
    }
    info(s"${valueCount + stuck} calls agree ($valueCount on a value, $stuck stuck), $skipped skipped for fuel, " +
      s"over $testedFunctions functions of ${files.size} files")
    assert(valueCount >= 1000 && stuck >= 50, s"only $valueCount values and $stuck stuck calls compared")
  }
}
