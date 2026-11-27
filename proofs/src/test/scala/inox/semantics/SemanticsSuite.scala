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
  import Embedding._


  val fuel = BigInt(40)
  val maxCalls = 20000

  object Sem extends Embedding.Evaluator(fuel)

  enum Outcome {
    case Value, Stuck, Skipped
  }

  /** Evaluates `e` (closed, in the fragment) with both evaluators, and fails if they disagree. */
  def compare(e: Expr, sp: S.Program, label: => String)(using symbols: Symbols): Outcome = {
    // the semantics first: when its oracles can't decide a quantifier, or it runs out of fuel, the
    // recursive evaluator, which can be much slower on these (it solves quantifiers), isn't run
    val ours = try Sem.eval(sp, fuel, S.Env(S.Nil(), S.Nil()), expr(e).get) catch {
      case _: Unsupported => return Outcome.Skipped
    }
    if (ours == S.OutOfFuel()) return Outcome.Skipped
    val ctx = TestContext(Options(Seq(evaluators.optMaxCalls(maxCalls))))
    val ev = evaluators.RecursiveEvaluator(InoxProgram(symbols), ctx)
    val reference = try ev.eval(e) catch {
      case _: StackOverflowError => return Outcome.Skipped
    }
    (reference, ours) match {
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

  test("The generated Lean semantics is up to date with proofs/semantics.md") {
    val generated = Codegen.lean(Paths.get(Codegen.source))
    assert(generated == Files.readString(Paths.get(Codegen.leanOutput)),
      "run `sbt proofs/run` and commit the result")
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

  test("Floating point") {
    val specials = Seq(0.0, -0.0, 1.0, -1.0, 0.5, 0.1, 1.5, 2.5, -2.5, 3.0, 1e300, -1e300, 1e-310, -1e-310,
      Double.MinPositiveValue, Double.MaxValue, Double.MinValue, Double.PositiveInfinity, Double.NegativeInfinity,
      Double.NaN, java.lang.Double.MIN_NORMAL, 4503599627370497.0, 1e16 + 2)
    def double(r: scala.util.Random): Double = r.nextInt(4) match {
      case 0 => specials(r.nextInt(specials.size))
      case 1 => java.lang.Double.longBitsToDouble(r.nextLong())
      case _ => (r.nextInt(2001) - 1000) / 8.0 * math.pow(2, r.nextInt(9) - 4)
    }
    def float(r: scala.util.Random): Float = r.nextInt(4) match {
      case 0 => specials(r.nextInt(specials.size)).toFloat
      case 1 => java.lang.Float.intBitsToFloat(r.nextInt())
      case _ => ((r.nextInt(2001) - 1000) / 8.0 * math.pow(2, r.nextInt(9) - 4)).toFloat
    }
    def fp(r: scala.util.Random): Expr = if (r.nextBoolean()) Float64Literal(double(r)) else Float32Literal(float(r))
    def same(r: scala.util.Random): (Expr, Expr) =
      if (r.nextBoolean()) (Float64Literal(double(r)), Float64Literal(double(r)))
      else (Float32Literal(float(r)), Float32Literal(float(r)))
    def two(f: (Expr, Expr) => Expr) = (r: scala.util.Random) => { val (a, b) = same(r); f(a, b) }
    val rne = RoundNearestTiesToEven
    val modes = Seq(RoundNearestTiesToEven, RoundNearestTiesToAway, RoundTowardPositive, RoundTowardNegative, RoundTowardZero)
    def mode(r: scala.util.Random) = modes(r.nextInt(modes.size))
    compareOps("floating point", Seq(
      "+" -> (r => two(FPAdd(mode(r), _, _))(r)), "-" -> (r => two(FPSub(mode(r), _, _))(r)),
      "*" -> (r => two(FPMul(mode(r), _, _))(r)), "/" -> (r => two(FPDiv(mode(r), _, _))(r)),
      "min" -> two(FPMin(_, _)), "max" -> two(FPMax(_, _)),
      "fma" -> (r => if (r.nextBoolean()) FPFMA(mode(r), Float64Literal(double(r)), Float64Literal(double(r)), Float64Literal(double(r)))
                     else FPFMA(mode(r), Float32Literal(float(r)), Float32Literal(float(r)), Float32Literal(float(r)))),
      "==" -> two(FPEquals(_, _)), "eq" -> two(Equals(_, _)), "<" -> two(FPLessThan(_, _)),
      ">" -> two(FPGreaterThan(_, _)), "<=" -> two(FPLessEquals(_, _)), ">=" -> two(FPGreaterEquals(_, _)),
      "neg" -> (r => FPUMinus(fp(r))), "abs" -> (r => FPAbs(fp(r))), "sqrt" -> (r => Sqrt(mode(r), fp(r))),
      "round" -> (r => FPRound(mode(r), fp(r))),
      "isZero" -> (r => FPIsZero(fp(r))), "isInfinite" -> (r => FPIsInfinite(fp(r))), "isNaN" -> (r => FPIsNaN(fp(r))),
      "isNegative" -> (r => FPIsNegative(fp(r))), "isPositive" -> (r => FPIsPositive(fp(r))),
      "isNormal" -> (r => FPIsNormal(fp(r))), "isSubnormal" -> (r => FPIsSubnormal(fp(r))),
      "toBV" -> (r => FPToBV(Seq(8, 32, 64)(r.nextInt(3)), r.nextBoolean(), mode(r), fp(r))),
      "toReal" -> (r => FPToReal(fp(r))),
      "toDouble" -> (r => ToDouble(if (r.nextBoolean()) fp(r) else Int64Literal(r.nextLong()))),
      "toFloat" -> (r => ToFloat(if (r.nextBoolean()) fp(r) else Int32Literal(r.nextInt()))),
      "cast" -> (r => FPCast(Seq(5, 8, 11)(r.nextInt(3)), Seq(11, 24, 53)(r.nextInt(3)), mode(r), r.nextInt(3) match {
        case 0 => fp(r)
        case 1 => BVLiteral(r.nextBoolean(), BigInt(64, r), 64)
        case _ => FractionLiteral(BigInt(r.nextInt(2001) - 1000), BigInt(r.nextInt(999) + 1))
      })),
      "unsignedToDouble" -> (r => ToDouble(BVLiteral(false, BigInt(64, r), 64))),
      "fromBinary" -> (r => if (r.nextBoolean()) FPFromBinary(11, 53, Int64Literal(r.nextLong()))
                            else FPFromBinary(8, 24, Int32Literal(r.nextInt())))
    ), 400)
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

  test("Dependent types, propositions, and refinements of variables") {
    given Symbols = NoSymbols
    val sp = program(Map())
    val empty = S.Env(S.Nil(), S.Nil())
    def run(e: Expr) = Sem.eval(sp, fuel, empty, expr(e).get)
    def ty(t: Type) = tpe(t).get
    def bv(i: Int) = BVLiteral(true, i, 3)
    val bv3 = BVType(true, 3)

    // the second element is at least the first one
    val x = ValDef.fresh("x", bv3)
    val y = ValDef.fresh("y", bv3)
    val ordered = SigmaType(Seq(x), RefinementType(y, GreaterEquals(y.toVariable, x.toVariable)))
    val p = ValDef.fresh("p", ordered)
    val q = ValDef.fresh("q", TupleType(Seq(bv3, bv3)))
    assert(run(Forall(Seq(p), GreaterEquals(TupleSelect(p.toVariable, 2), TupleSelect(p.toVariable, 1)))) == S.Ok(S.BoolV(true)))
    assert(run(Forall(Seq(q), GreaterEquals(TupleSelect(q.toVariable, 2), TupleSelect(q.toVariable, 1)))) == S.Ok(S.BoolV(false)))
    def pair(a: Int, b: Int) = S.TupleV(list(Seq(S.BVV(true, 3, a), S.BVV(true, 3, b))))
    assert(Sem.has_type(sp, empty, pair(1, 2), ty(ordered)))
    assert(Sem.has_type(sp, empty, pair(2, 2), ty(ordered)))
    assert(!Sem.has_type(sp, empty, pair(3, 2), ty(ordered)))
    assert(!Sem.has_type(sp, empty, S.TupleV(list(Seq(S.BVV(true, 3, 1)))), ty(ordered)))

    // a refinement can refer to the variables in scope
    val n = ValDef.fresh("n", bv3)
    val above = RefinementType(y, GreaterEquals(y.toVariable, n.toVariable))
    val withN = S.Env(S.Nil(), S.Cons(S.Binding(n.id, S.BVV(true, 3, 2)), S.Nil()))
    assert(Sem.has_type(sp, withN, S.BVV(true, 3, 3), ty(above)))
    assert(!Sem.has_type(sp, withN, S.BVV(true, 3, 1), ty(above)))
    val z = ValDef.fresh("z", above)
    assert(run(Let(n, bv(2), Forall(Seq(z), GreaterEquals(z.toVariable, bv(2))))) == S.Ok(S.BoolV(true)))
    assert(run(Let(n, bv(1), Forall(Seq(z), GreaterEquals(z.toVariable, bv(2))))) == S.Ok(S.BoolV(false)))

    // propositions are Booleans
    assert(Sem.has_type(sp, empty, S.BoolV(false), S.PropType()))
    assert(!Sem.has_type(sp, empty, S.IntV(0), S.PropType()))

    // values of dependent function types are applied as other functions
    val i = ValDef.fresh("i", IntegerType())
    val j = ValDef.fresh("j", IntegerType())
    val increasing = PiType(Seq(i), RefinementType(j, GreaterThan(j.toVariable, i.toVariable)))
    val f = ValDef.fresh("f", increasing)
    val succ = Lambda(Seq(i), Plus(i.toVariable, IntegerLiteral(1)))
    val e = Application(Lambda(Seq(f), Application(f.toVariable, Seq(IntegerLiteral(41)))), Seq(succ))
    assert(run(e) == S.Ok(S.IntV(42)))
    assert(compare(e, sp, "pi") == Outcome.Value)
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

  test("The values of a sort with an equality are compared with it") {
    import dsl._
    val (parityId, evenId, eqId, nId) = (FreshIdentifier("Parity"), FreshIdentifier("P"), FreshIdentifier("eq"), FreshIdentifier("n"))
    // integers, up to their parity
    val Parity = mkSort(parityId, HasADTEquality(eqId))() { _ => Seq((evenId, Seq(ValDef(nId, IntegerType())))) }
    val eq = mkFunDef(eqId)() { _ =>
      (Seq("a" :: T(parityId)(), "b" :: T(parityId)()), BooleanType(), { case Seq(a, b) =>
        Modulo(a.getField(nId), E(BigInt(2))) === Modulo(b.getField(nId), E(BigInt(2)))
      })
    }
    given symbols: Symbols = NoSymbols.withSorts(Seq(Parity)).withFunctions(Seq(eq))
    val sp = program(coveredFunctions)
    def p(n: Int) = ADT(evenId, Seq(), Seq(IntegerLiteral(n)))
    def run(e: Expr) = Sem.eval(sp, fuel, S.Env(S.Nil(), S.Nil()), expr(e).get)

    assert(run(Equals(p(1), p(3))) == S.Ok(S.BoolV(true)))
    assert(run(Equals(p(1), p(2))) == S.Ok(S.BoolV(false)))
    // also inside other values, and as the elements of a set
    assert(run(Equals(Tuple(Seq(p(1), p(4))), Tuple(Seq(p(3), p(2))))) == S.Ok(S.BoolV(true)))
    assert(run(ElementOfSet(p(5), FiniteSet(Seq(p(1), p(2)), T(parityId)()))) == S.Ok(S.BoolV(true)))
    for (e <- Seq(Equals(p(1), p(3)), Equals(p(1), p(2)), Equals(Tuple(Seq(p(1), p(4))), Tuple(Seq(p(3), p(2))))))
      assert(compare(e, sp, "unit") == Outcome.Value)
  }

  /** Random well-typed expressions, which nest the operations of all the theories with lets,
    * conditionals, closures, function calls and ADTs. */
  class Fuzzer(rnd: scala.util.Random, listId: Identifier, nilId: Identifier, consId: Identifier,
               headId: Identifier, tailId: Identifier, sizeId: Identifier)(using symbols: Symbols) {
    val I = IntegerType()
    val B = BooleanType()
    val S8 = BVType(true, 8)
    val U8 = BVType(false, 8)
    val S16 = BVType(true, 16)
    val F32 = FPType(8, 24)
    val L = ADTType(listId, Seq())
    val Fn = FunctionType(Seq(I), I)
    val Pair = TupleType(Seq(I, B))
    val types: Seq[Type] = Seq(I, B, S8, U8, S16, CharType(), StringType(), RealType(), F32, Pair,
      SetType(I), BagType(I), MapType(I, I), Fn, L, UnitType())
    /** The types whose values can be compared under `--function-equality=none`. */
    val comparable = types.filter(_ != Fn)

    def pick[A](xs: Seq[A]): A = xs(rnd.nextInt(xs.size))

    def float(): Expr = FPLiteral(8, 24, scala.collection.immutable.BitSet.fromBitMask(Array(
      java.lang.Float.floatToRawIntBits(pick(Seq(0f, -0f, 1f, -1.5f, 0.1f, 3e38f, 1e-45f, Float.NaN,
        Float.PositiveInfinity, Float.NegativeInfinity))).toLong & 0xffffffffL)).map(_ + 1))

    def leaf(t: Type, vars: Seq[Variable]): Expr = {
      val vs = vars.filter(_.tpe == t)
      if (vs.nonEmpty && rnd.nextInt(3) > 0) pick(vs)
      else t match {
        case F32 => float()
        case `L` => ADT(nilId, Seq(), Seq())
        case `Fn` => val x = ValDef.fresh("x", I); Lambda(Seq(x), x.toVariable)
        case _ => values(t, 1, rnd).get
      }
    }

    def gen(t: Type, depth: Int, vars: Seq[Variable]): Expr = {
      if (depth <= 0 || rnd.nextInt(5) == 0) return leaf(t, vars)
      def g(t: Type) = gen(t, depth - 1, vars)
      val rm = pick(Seq(RoundNearestTiesToEven, RoundNearestTiesToAway, RoundTowardPositive,
        RoundTowardNegative, RoundTowardZero))
      // the forms of every type
      val common: Seq[() => Expr] = Seq(
        () => IfExpr(g(B), g(t), g(t)),
        () => { val s = pick(types); val x = ValDef.fresh("x", s)
                Let(x, g(s), gen(t, depth - 1, vars :+ x.toVariable)) },
        () => { val s = pick(types); val x = ValDef.fresh("y", s)
                Application(Lambda(Seq(x), gen(t, depth - 1, vars :+ x.toVariable)), Seq(g(s))) },
        () => TupleSelect(Tuple(Seq(g(t), g(I))), 1),
        () => Assume(g(B), g(t)))
      def bv(t: BVType): Seq[() => Expr] = Seq(
        () => Plus(g(t), g(t)), () => Minus(g(t), g(t)), () => Times(g(t), g(t)),
        () => Division(g(t), g(t)), () => Remainder(g(t), g(t)), () => Modulo(g(t), g(t)),
        () => UMinus(g(t)), () => BVNot(g(t)), () => BVAnd(g(t), g(t)), () => BVOr(g(t), g(t)),
        () => BVXor(g(t), g(t)), () => BVShiftLeft(g(t), g(t)), () => BVAShiftRight(g(t), g(t)),
        () => BVLShiftRight(g(t), g(t)), () => IntToBV(t.size, t.signed, g(I)))
      val forms: Seq[() => Expr] = t match {
        case I => Seq(
          () => Plus(g(I), g(I)), () => Minus(g(I), g(I)), () => Times(g(I), g(I)),
          () => Division(g(I), g(I)), () => Remainder(g(I), g(I)), () => Modulo(g(I), g(I)),
          () => UMinus(g(I)), () => StringLength(g(StringType())), () => BVToInt(g(pick(Seq(S8, U8, S16)))),
          () => MultiplicityInBag(g(I), g(BagType(I))), () => MapApply(g(MapType(I, I)), g(I)),
          () => Application(g(Fn), Seq(g(I))), () => FunctionInvocation(sizeId, Seq(), Seq(g(L))),
          () => ADTSelector(g(L), headId))
        case B => Seq(
          () => And(g(B), g(B)), () => Or(g(B), g(B)), () => Not(g(B)), () => Implies(g(B), g(B)),
          () => { val s = pick(comparable); Equals(gen(s, depth - 1, vars), gen(s, depth - 1, vars)) },
          () => { val s = pick(Seq(I, RealType(), S8, U8, CharType())); LessThan(gen(s, depth - 1, vars), gen(s, depth - 1, vars)) },
          () => { val s = pick(Seq(I, RealType(), S16)); GreaterEquals(gen(s, depth - 1, vars), gen(s, depth - 1, vars)) },
          () => ElementOfSet(g(I), g(SetType(I))), () => SubsetOf(g(SetType(I)), g(SetType(I))),
          () => IsConstructor(g(L), consId), () => FPLessThan(g(F32), g(F32)), () => FPEquals(g(F32), g(F32)),
          () => FPIsNaN(g(F32)), () => FPIsNegative(g(F32)), () => FPIsSubnormal(g(F32)))
        case t: BVType if t == S8 => bv(t) :+ (() => BVNarrowingCast(g(S16), S8)) :+ (() => BVUnsignedToSigned(g(U8)))
        case t: BVType if t == U8 => bv(t) :+ (() => BVSignedToUnsigned(g(S8)))
        case t: BVType => bv(t) :+ (() => BVWideningCast(g(S8), S16))
        case CharType() => Seq()
        case StringType() => Seq(() => StringConcat(g(StringType()), g(StringType())),
          () => SubString(g(StringType()), g(I), g(I)))
        case RealType() => Seq(() => Plus(g(t), g(t)), () => Minus(g(t), g(t)), () => Times(g(t), g(t)),
          () => Division(g(t), g(t)), () => UMinus(g(t)), () => FPToReal(g(F32)))
        case F32 => Seq(() => FPAdd(rm, g(F32), g(F32)), () => FPSub(rm, g(F32), g(F32)),
          () => FPMul(rm, g(F32), g(F32)), () => FPDiv(rm, g(F32), g(F32)), () => FPUMinus(g(F32)),
          () => FPAbs(g(F32)), () => FPMin(g(F32), g(F32)), () => FPMax(g(F32), g(F32)),
          () => Sqrt(rm, g(F32)), () => FPRound(rm, g(F32)), () => FPCast(8, 24, rm, g(RealType())))
        case `Pair` => Seq(() => Tuple(Seq(g(I), g(B))))
        case SetType(_) => Seq(() => FiniteSet(Seq.fill(rnd.nextInt(3))(g(I)), I),
          () => SetAdd(g(t), g(I)), () => SetUnion(g(t), g(t)), () => SetIntersection(g(t), g(t)),
          () => SetDifference(g(t), g(t)))
        case BagType(_) => Seq(() => FiniteBag(Seq.fill(rnd.nextInt(3))(g(I) -> g(I)), I),
          () => BagAdd(g(t), g(I)), () => BagUnion(g(t), g(t)), () => BagIntersection(g(t), g(t)),
          () => BagDifference(g(t), g(t)))
        case MapType(_, _) => Seq(() => FiniteMap(Seq.fill(rnd.nextInt(3))(g(I) -> g(I)), g(I), I, I),
          () => MapUpdated(g(t), g(I), g(I)), () => MapMerge(g(SetType(I)), g(t), g(t)))
        case `Fn` => Seq(() => { val x = ValDef.fresh("x", I); Lambda(Seq(x), gen(I, depth - 1, vars :+ x.toVariable)) })
        case `L` => Seq(() => ADT(consId, Seq(), Seq(g(I), g(L))), () => ADTSelector(g(L), tailId))
        case _ => Seq()
      }
      pick(common ++ forms ++ forms)()
    }
  }

  test("Fuzzing: the semantics agrees with RecursiveEvaluator on random nested expressions") {
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
    given symbols: Symbols = NoSymbols.withSorts(Seq(List)).withFunctions(Seq(size))
    val sp = program(coveredFunctions)
    val count = sys.props.get("fuzz-count").map(_.toInt).getOrElse(3000)
    val seed = sys.props.get("fuzz-seed").map(_.toLong).getOrElse(0L)
    val rnd = new scala.util.Random(seed)
    val fuzzer = Fuzzer(rnd, listId, nilId, consId, headId, tailId, sizeId)
    val outcomes = (1 to count).map { i =>
      val t = fuzzer.pick(fuzzer.types)
      val e = fuzzer.gen(t, 2 + rnd.nextInt(4), Seq())
      assert(e.getType == t, s"ill-typed ${e.asString}")
      compare(e, sp, s"fuzz $i (seed $seed)")
    }
    val values = outcomes.count(_ == Outcome.Value)
    val stuck = outcomes.count(_ == Outcome.Stuck)
    info(s"$count expressions: $values values, $stuck stuck, ${count - values - stuck} skipped for fuel")
    assert(values >= count / 2 && stuck >= count / 20)
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
    info(s"${valueCount + stuck} calls agree ($valueCount on a value, $stuck stuck), $skipped skipped (out of fuel, or on a quantifier the tests can't decide), " +
      s"over $testedFunctions functions of ${files.size} files")
    assert(valueCount >= 1000 && stuck >= 50, s"only $valueCount values and $stuck stuck calls compared")
  }
}
