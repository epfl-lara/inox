/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

/** Unit tests of the local simplifications and normal forms of [[ExprOps]] and [[SymbolOps]],
  * and of [[Paths]].
  */
class SimplificationsSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.exprOps._
  import dsl._

  given ctx: Context = TestContext.empty

  val x = Variable.fresh("x", IntegerType())
  val y = Variable.fresh("y", IntegerType())
  val z = Variable.fresh("z", IntegerType())
  val a = Variable.fresh("a", Int32Type())
  val b = Variable.fresh("b", Int32Type())
  val p = Variable.fresh("p", BooleanType())
  val q = Variable.fresh("q", BooleanType())
  val r = Variable.fresh("r", BooleanType())
  val s = Variable.fresh("s", StringType())

  val listID = FreshIdentifier("List")
  val consID = FreshIdentifier("Cons")
  val nilID = FreshIdentifier("Nil")
  val headID = FreshIdentifier("head")
  val tailID = FreshIdentifier("tail")

  val listSort: ADTSort = mkSort(listID)("A") {
    case Seq(aT) => Seq(
      (consID, Seq(ValDef(headID, aT), ValDef(tailID, ADTType(listID, Seq(aT))))),
      (nilID, Seq())
    )
  }

  // An enumeration with two constructors, of two values each
  val twoID = FreshIdentifier("Two")
  val leftID = FreshIdentifier("Left")
  val rightID = FreshIdentifier("Right")
  val twoSort: ADTSort = mkSort(twoID)() { _ =>
    Seq(
      (leftID, Seq(ValDef(FreshIdentifier("l"), BooleanType()))),
      (rightID, Seq(ValDef(FreshIdentifier("r"), BooleanType())))
    )
  }

  // A sort without any finite value
  val loopID = FreshIdentifier("Loop")
  val loopConsID = FreshIdentifier("LoopCons")
  val loopSort: ADTSort = mkSort(loopID)() { _ =>
    Seq((loopConsID, Seq(ValDef(FreshIdentifier("next"), ADTType(loopID, Seq())))))
  }

  val symbols = NoSymbols.withSorts(Seq(listSort, twoSort, loopSort))
  given Symbols = symbols

  val program = InoxProgram(symbols)
  given program.symbols.Semantics = program.getSemantics

  val evaluator = evaluators.RecursiveEvaluator(program, ctx)

  private def eval(e: Expr, env: Map[Variable, Expr]): Expr =
    evaluator.eval(exprOps.replaceFromSymbols(env, e)).result.getOrElse(fail(s"Couldn't evaluate $e"))

  private def bigIntEnvs: Seq[Map[Variable, Expr]] = for {
    xv <- Seq(-7, -1, 0, 1, 3)
    yv <- Seq(-2, 0, 5)
    zv <- Seq(-3, 4)
  } yield Map(x -> IntegerLiteral(xv), y -> IntegerLiteral(yv), z -> IntegerLiteral(zv))

  /** Checks that `simplifyArithmetic` turns `e` into `expected` and preserves its value. */
  private def checkArith(e: Expr, expected: Expr, envs: Seq[Map[Variable, Expr]] = bigIntEnvs): Unit = {
    val simplified = simplifyArithmetic(e)
    assert(simplified == expected, s"for $e")
    assert(simplified.getType == e.getType, s"for $e")
    for (env <- envs) assert(eval(simplified, env) == eval(e, env), s"for $e with $env")
  }

  test("simplifyArithmetic on integers") {
    def i(n: Int) = IntegerLiteral(n)
    checkArith(i(3) + i(2), i(5))
    checkArith(i(0) + x, x)
    checkArith(x + i(0), x)
    checkArith(x + UMinus(y), x - y)
    checkArith((x + i(1)) + i(2), x + i(3))
    checkArith((i(1) + x) + i(2), i(3) + x)
    checkArith(x - i(0), x)
    checkArith(i(0) - x, UMinus(x))
    checkArith(i(3) - i(5), i(-2))
    checkArith(x - UMinus(y), x + y)
    checkArith(x - (UMinus(y) - z), x + (y + z))
    checkArith(UMinus(i(4)), i(-4))
    checkArith(UMinus(UMinus(x)), x)
    checkArith(UMinus(UMinus(x) + y), x - y)
    checkArith(UMinus(x - y), y - x)
    checkArith(i(3) * i(4), i(12))
    checkArith(i(1) * x, x)
    checkArith(i(-1) * x, UMinus(x))
    checkArith(x * i(1), x)
    checkArith(i(0) * x, i(0))
    checkArith(x * i(0), i(0))
    checkArith(i(2) * (i(3) * x), i(6) * x)
    checkArith(i(2) * (x * i(3)), i(6) * x)
    checkArith(i(2) * UMinus(x), i(-2) * x)
    checkArith(UMinus(x) * i(2), x * i(-2))
    checkArith(i(7) / i(2), i(3))
    // integer division is euclidean, as in SMT-LIB
    checkArith(i(-7) / i(2), i(-4))
    checkArith(i(7) / i(-2), i(-3))
    checkArith(i(-7) / i(-2), i(4))
    checkArith(x / i(1), x)
    checkArith(x / i(0), x / i(0), envs = Seq())
    checkArith(UMinus(x + y) + x, UMinus(y))
    checkArith(UMinus(x + y) + y, UMinus(x))
    checkArith(x - x, i(0))
    checkArith((x + y) - (y + x), i(0))
    checkArith((x + y) - ((y + x) + z), UMinus(z))
    // simplifications apply bottom-up until a fixpoint is reached
    checkArith((x + (i(1) + i(1))) * (i(2) - i(1)), x + i(2))
  }

  test("simplifyArithmetic keeps divisions that round") {
    def i(n: Int) = IntegerLiteral(n)
    // 2 * (x / 2) is not x when x is odd
    checkArith(i(2) * (x / i(2)), i(2) * (x / i(2)))
    checkArith(i(4) * (x / i(2)), i(4) * (x / i(2)))
  }

  test("simplifyArithmetic on bit-vectors") {
    def i(n: Int) = Int32Literal(n)
    val envs = for (av <- Seq(-5, 0, 7, Int.MaxValue); bv <- Seq(-1, 2))
      yield Map(a -> Int32Literal(av), b -> Int32Literal(bv))
    checkArith(i(3) + i(2), i(5), envs)
    checkArith(i(Int.MaxValue) + i(1), i(Int.MinValue), envs)
    checkArith((a + i(1)) + i(2), a + i(3), envs)
    checkArith(i(1) * a, a, envs)
    checkArith(i(-7) / i(2), i(-3), envs)
    checkArith(a - a, i(0), envs)
    checkArith((a + b) - (b + a), i(0), envs)
    checkArith(UMinus(a + b) + a, UMinus(b), envs)
    checkArith(i(2) * (a / i(2)), i(2) * (a / i(2)), envs)

    val u = Variable.fresh("u", BVType(false, 8))
    def ui(n: Int) = BVLiteral(false, n, 8)
    val uEnvs = Seq(0, 1, 200).map(n => Map(u -> ui(n)))
    checkArith(ui(250) + ui(10), ui(4), uEnvs)
    checkArith(ui(0) - u, UMinus(u), uEnvs)
    checkArith(u - u, ui(0), uEnvs)
  }

  test("simplifyArithmetic on strings") {
    val envs = Seq(Map(s -> StringLiteral("s")))
    checkArith(StringConcat(StringLiteral(""), s), s, envs)
    checkArith(StringConcat(s, StringLiteral("")), s, envs)
    checkArith(StringConcat(StringLiteral("a"), StringLiteral("b")), StringLiteral("ab"), envs)
    checkArith(StringConcat(StringLiteral("a"), StringConcat(StringLiteral("b"), s)),
      StringConcat(StringLiteral("ab"), s), envs)
    checkArith(StringConcat(StringConcat(s, StringLiteral("a")), StringLiteral("b")),
      StringConcat(s, StringLiteral("ab")), envs)
    checkArith(StringConcat(s, StringConcat(s, s)), StringConcat(StringConcat(s, s), s), envs)
  }

  test("simplifyString") {
    def str(v: String) = StringLiteral(v)
    assert(simplifyString(StringConcat(str(""), s)) == s)
    assert(simplifyString(StringConcat(s, str(""))) == s)
    assert(simplifyString(StringConcat(StringConcat(str("a"), str("b")), str("c"))) == str("abc"))
    assert(simplifyString(StringLength(StringConcat(str("ab"), str("c")))) == IntegerLiteral(3))
    assert(simplifyString(SubString(str("hello"), IntegerLiteral(1), IntegerLiteral(3))) == str("el"))
    assert(simplifyString(StringConcat(s, str("a"))) == StringConcat(s, str("a")))
  }

  test("simplifyString leaves out of bounds substrings to the evaluator") {
    for ((start, end) <- Seq((2, 10), (-1, 2), (3, 1), (6, 7))) {
      val e = SubString(StringLiteral("hello"), IntegerLiteral(start), IntegerLiteral(end))
      assert(simplifyString(e) == e)
    }
  }

  test("negate") {
    assert(negate(Not(p)) == p)
    assert(negate(Implies(p, q)) == And(p, Not(q)))
    assert(negate(Or(p, q)) == And(Not(p), Not(q)))
    assert(negate(And(p, q)) == Or(Not(p), Not(q)))
    assert(negate(LessThan(x, y)) == GreaterEquals(x, y))
    assert(negate(LessEquals(x, y)) == GreaterThan(x, y))
    assert(negate(GreaterThan(x, y)) == LessEquals(x, y))
    assert(negate(GreaterEquals(x, y)) == LessThan(x, y))
    assert(negate(IfExpr(p, q, r)) == IfExpr(p, Not(q), Not(r)))
    assert(negate(BooleanLiteral(true)) == BooleanLiteral(false))
    assert(negate(Let(x.toVal, y, Equals(x, z))) == Let(x.toVal, y, Not(Equals(x, z))))
    assert(negate(Equals(x, y)) == Not(Equals(x, y)))
  }

  test("toCNF") {
    assert(toCNF(And(p, q)) == Seq(p, q))
    assert(toCNF(Or(And(p, q), r)) == Seq(Or(p, r), Or(q, r)))
    assert(toCNF(Or(p, And(q, r))) == Seq(Or(p, q), Or(p, r)))
    assert(toCNF(Implies(p, q)) == Seq(Or(Not(p), q)))
    assert(toCNF(Not(Or(p, q))) == Seq(Not(p), Not(q)))
    assert(toCNF(Not(Implies(p, q))) == Seq(p, Not(q)))
    assert(toCNF(Not(Not(p))) == Seq(p))
    assert(toCNF(Not(And(p, q))) == Seq(Or(Not(p), Not(q))))
    assert(toCNF(IfExpr(p, q, r)) == Seq(Or(Not(p), q), Or(p, r)))
    assert(toCNF(Let(x.toVal, y, And(p, Equals(x, z)))) == Seq(Let(x.toVal, y, p), Let(x.toVal, y, Equals(x, z))))
    assert(toCNF(Equals(x, y)) == Seq(Equals(x, y)))
  }

  test("normalizeFraction and floor") {
    assert(normalizeFraction(FractionLiteral(4, 6)) == FractionLiteral(2, 3))
    assert(normalizeFraction(FractionLiteral(4, -6)) == FractionLiteral(-2, 3))
    assert(normalizeFraction(FractionLiteral(-4, -6)) == FractionLiteral(2, 3))
    assert(normalizeFraction(FractionLiteral(0, -6)) == FractionLiteral(0, 1))
    assert(floor(FractionLiteral(7, 2)) == FractionLiteral(3, 1))
    assert(floor(FractionLiteral(-7, 2)) == FractionLiteral(-4, 1))
    assert(floor(FractionLiteral(-6, 2)) == FractionLiteral(-3, 1))
    assert(floor(FractionLiteral(0, 5)) == FractionLiteral(0, 1))
    assertThrows[IllegalStateException](floor(FractionLiteral(1, 0)))
  }

  test("occursIn") {
    assert(occursIn(x.toVal, x + y))
    assert(!occursIn(x.toVal, y + z))
    assert(!occursIn(x.toVal, Lambda(Seq(x.toVal), x)))
    assert(!occursIn(x.toVal, Forall(Seq(x.toVal), Equals(x, y))))
    assert(!occursIn(x.toVal, Choose(x.toVal, Equals(x, y))))
    assert(!occursIn(x.toVal, Let(x.toVal, y, x)))
    assert(occursIn(x.toVal, Let(y.toVal, x, y)))
  }

  test("isGround, isSimple and containsFunctionCalls") {
    val fd = mkFunDef(FreshIdentifier("f"))() { _ => (Seq("n" :: IntegerType()), IntegerType(), { case Seq(n) => n }) }
    val call = FunctionInvocation(fd.id, Seq(), Seq(x))
    assert(isGround(IntegerLiteral(1) + IntegerLiteral(2)))
    assert(!isGround(x + IntegerLiteral(2)))
    assert(isSimple(x + y))
    assert(!isSimple(call))
    assert(!isSimple(Lambda(Seq(x.toVal), x)))
    assert(containsFunctionCalls(x + call))
    assert(!containsFunctionCalls(x + y))
    assert(functionCallsOf(call + call) == Set(call))
  }

  test("simplifyLets") {
    val v = Variable.fresh("v", IntegerType())
    val w = Variable.fresh("w", IntegerType())
    val t = Variable.fresh("t", TupleType(Seq(IntegerType(), IntegerType())))
    val ts = Variable.fresh("ts", TupleType(Seq(IntegerType(), IntegerType())))
    // let v = (let w = x * y in w + w) in v + v  ~>  let w = x * y in let v = w + w in v + v
    assert(symbols.simplifyLets(Let(v.toVal, Let(w.toVal, x * y, w + w), v + v)) ==
      Let(w.toVal, x * y, Let(v.toVal, w + w, v + v)))
    assert(symbols.simplifyLets(Let(v.toVal, x * y, v)) == x * y)
    assert(symbols.simplifyLets(Let(v.toVal, x, v + v)) == x + x)
    assert(symbols.simplifyLets(Let(v.toVal, TupleSelect(t, 1), v + v)) == TupleSelect(t, 1) + TupleSelect(t, 1))
    assert(symbols.simplifyLets(Let(ts.toVal, t, TupleSelect(ts, 2))) == TupleSelect(t, 2))
    val set = Variable.fresh("set", SetType(IntegerType()))
    assert(symbols.simplifyLets(Let(set.toVal, FiniteSet(Seq(), IntegerType()), ElementOfSet(x, set))) ==
      ElementOfSet(x, FiniteSet(Seq(), IntegerType())))
    // complex values aren't duplicated
    assert(symbols.simplifyLets(Let(v.toVal, x * y, v + v)) == Let(v.toVal, x * y, v + v))
  }

  test("expandLets") {
    val v = Variable.fresh("v", IntegerType())
    val w = Variable.fresh("w", IntegerType())
    assert(symbols.expandLets(Let(v.toVal, x * y, Let(w.toVal, v + v, w * v))) ==
      ((x * y) + (x * y)) * (x * y))
    assert(symbols.expandLets(IfExpr(p, Let(v.toVal, x, v), y)) == IfExpr(p, x, y))
    assert(symbols.expandLets(x + y) == x + y)
  }

  test("liftLets") {
    val v = Variable.fresh("v", IntegerType())
    val w = Variable.fresh("w", IntegerType())
    assert(symbols.liftLets(Plus(Let(v.toVal, x, v), Let(w.toVal, y, w))) ==
      Let(v.toVal, x, Let(w.toVal, y, v + w)))
    assert(symbols.liftLets(Let(v.toVal, Let(w.toVal, x, w + w), v * v)) ==
      Let(w.toVal, x, Let(v.toVal, w + w, v * v)))
  }

  test("liftLets doesn't lift lets out of the scope of their variables") {
    val v = Variable.fresh("v", IntegerType())
    val lambda = Lambda(Seq(x.toVal), Let(v.toVal, x + y, v * v))
    val lifted = symbols.liftLets(lambda)
    assert(exprOps.variablesOf(lifted) == Set(y), s"in $lifted")
    val forall = Forall(Seq(x.toVal), Let(v.toVal, x + y, Equals(v, v)))
    val liftedForall = symbols.liftLets(forall)
    assert(exprOps.variablesOf(liftedForall) == Set(y), s"in $liftedForall")
  }

  test("hoistIte") {
    assert(symbols.hoistIte(Plus(IfExpr(p, x, y), z)) == IfExpr(p, x + z, y + z))
    assert(symbols.hoistIte(Plus(IfExpr(p, x, y), IfExpr(q, y, z))) ==
      IfExpr(p, IfExpr(q, x + y, x + z), IfExpr(q, y + y, y + z)))
    assert(symbols.hoistIte(x + y) == x + y)
  }

  test("hoistIte doesn't hoist conditions out of the scope of their variables") {
    val v = Variable.fresh("v", IntegerType())
    val lambda = Lambda(Seq(x.toVal), IfExpr(x > IntegerLiteral(0), x, y))
    val hoisted = symbols.hoistIte(lambda)
    assert(exprOps.variablesOf(hoisted) == Set(y), s"in $hoisted")
    val let = Let(v.toVal, x, Plus(IfExpr(v > IntegerLiteral(0), v, y), z))
    val hoistedLet = symbols.hoistIte(let)
    assert(exprOps.variablesOf(hoistedLet) == Set(x, y, z), s"in $hoistedLet")
    for (xv <- Seq(-1, 1); env = Map(x -> IntegerLiteral(xv), y -> IntegerLiteral(7), z -> IntegerLiteral(2)))
      assert(eval(hoistedLet, env) == eval(let, env))
  }

  test("simplifyByConstructors") {
    val e = And(Seq(p, BooleanLiteral(true), Or(q, BooleanLiteral(false))))
    assert(symbols.simplifyByConstructors(e) == And(p, q))
    assert(symbols.simplifyByConstructors(Not(Not(p))) == p)
    assert(symbols.simplifyByConstructors(IfExpr(BooleanLiteral(true), x, y)) == x)
  }

  test("simplestValue") {
    val T = TypeParameter.fresh("T")
    assert(program.symbols.simplestValue(StringType()) == StringLiteral(""))
    assert(program.symbols.simplestValue(Int8Type()) == Int8Literal(0))
    assert(program.symbols.simplestValue(Float32Type()) == FPLiteral.plusZero(8, 24))
    assert(program.symbols.simplestValue(RealType()) == FractionLiteral(0, 1))
    assert(program.symbols.simplestValue(CharType()) == CharLiteral('a'))
    assert(program.symbols.simplestValue(UnitType()) == UnitLiteral())
    assert(program.symbols.simplestValue(BagType(IntegerType())) == FiniteBag(Seq(), IntegerType()))
    assert(program.symbols.simplestValue(MapType(IntegerType(), BooleanType())) ==
      FiniteMap(Seq(), BooleanLiteral(false), IntegerType(), BooleanType()))
    assert(program.symbols.simplestValue(TupleType(Seq(IntegerType(), BooleanType()))) ==
      Tuple(Seq(IntegerLiteral(0), BooleanLiteral(false))))
    assert(program.symbols.simplestValue(T) == GenericValue(T, 0))
    assert(program.symbols.simplestValue(ADTType(listID, Seq(IntegerType()))) == ADT(nilID, Seq(IntegerType()), Seq()))
    assert(program.symbols.simplestValue(ADTType(twoID, Seq())) == ADT(leftID, Seq(), Seq(BooleanLiteral(false))))
    program.symbols.simplestValue(FunctionType(Seq(IntegerType()), IntegerType())) match {
      case Lambda(params, IntegerLiteral(zero)) => assert(params.map(_.getType) == Seq(IntegerType()) && zero == 0)
      case e => fail(s"Unexpected simplest function $e")
    }
    assertThrows[program.symbols.NoSimpleValue](program.symbols.simplestValue(ADTType(loopID, Seq())))
    assertThrows[program.symbols.NoSimpleValue](program.symbols.simplestValue(Untyped))
  }

  test("hasInstance") {
    assert(symbols.hasInstance(IntegerType()) == Some(true))
    assert(symbols.hasInstance(ADTType(listID, Seq(IntegerType()))) == Some(true))
    assert(symbols.hasInstance(ADTType(loopID, Seq())) == Some(false))
    assert(symbols.hasInstance(TypeParameter.fresh("T")) == None)
    assert(symbols.hasInstance(TupleType(Seq(IntegerType(), BooleanType()))) == Some(true))
    assert(symbols.hasInstance(MapType(IntegerType(), TypeParameter.fresh("T"))) == None)
  }

  /** Checks that `constructExpr` builds `count` distinct values of type `tpe`. */
  private def checkConstructExpr(tpe: Type, count: Int): Unit = {
    val values = (0 until count).map(i => symbols.constructExpr(i, tpe))
    for (v <- values) assert(symbols.isValueOfType(v, tpe), s"$v is not a value of type $tpe")
    assert(values.distinct.size == count, s"Values of $tpe aren't distinct: $values")
  }

  test("constructExpr") {
    checkConstructExpr(BooleanType(), 2)
    checkConstructExpr(IntegerType(), 10)
    checkConstructExpr(Int8Type(), 10)
    checkConstructExpr(CharType(), 10)
    checkConstructExpr(RealType(), 10)
    checkConstructExpr(UnitType(), 1)
    checkConstructExpr(TypeParameter.fresh("T"), 10)
    checkConstructExpr(TupleType(Seq(IntegerType(), BooleanType())), 10)
    checkConstructExpr(TupleType(Seq(BooleanType(), BooleanType())), 4)
    checkConstructExpr(TupleType(Seq(BooleanType(), UnitType(), BooleanType())), 4)
    checkConstructExpr(SetType(IntegerType()), 10)
    checkConstructExpr(SetType(BooleanType()), 4)
    checkConstructExpr(BagType(IntegerType()), 10)
    checkConstructExpr(MapType(IntegerType(), IntegerType()), 10)
    checkConstructExpr(MapType(IntegerType(), BooleanType()), 10)
    checkConstructExpr(MapType(BooleanType(), BooleanType()), 4)
    checkConstructExpr(MapType(UnitType(), BooleanType()), 2)
    checkConstructExpr(MapType(BooleanType(), UnitType()), 1)
    checkConstructExpr(ADTType(listID, Seq(IntegerType())), 10)
    checkConstructExpr(ADTType(twoID, Seq()), 4)
    checkConstructExpr(FunctionType(Seq(), BooleanType()), 2)
    checkConstructExpr(FunctionType(Seq(IntegerType()), IntegerType()), 5)
  }

  test("constructExpr rejects indices beyond the type's cardinality") {
    assertThrows[FatalError](symbols.constructExpr(2, BooleanType()))
    assertThrows[FatalError](symbols.constructExpr(4, ADTType(twoID, Seq())))
    assertThrows[FatalError](symbols.constructExpr(16, SetType(TupleType(Seq(BooleanType(), BooleanType())))))
  }

  test("typeCardinality") {
    assert(symbols.typeCardinality(BooleanType()) == Some(2))
    assert(symbols.typeCardinality(TupleType(Seq(BooleanType(), BooleanType()))) == Some(4))
    assert(symbols.typeCardinality(SetType(BooleanType())) == Some(4))
    assert(symbols.typeCardinality(MapType(BooleanType(), BooleanType())) == Some(4))
    assert(symbols.typeCardinality(ADTType(twoID, Seq())) == Some(4))
    assert(symbols.typeCardinality(ADTType(listID, Seq(BooleanType()))) == None)
    assert(symbols.typeCardinality(IntegerType()) == None)
    assert(symbols.typeCardinality(FunctionType(Seq(), BooleanType())) == Some(2))
    // a bag can hold its single element any number of times
    assert(symbols.typeCardinality(BagType(UnitType())) == None)
    assert(symbols.typeCardinality(BagType(Untyped)) == Some(1))
  }

  test("isValue") {
    assert(symbols.isValue(IntegerLiteral(1)))
    assert(symbols.isValue(Tuple(Seq(IntegerLiteral(1), BooleanLiteral(true)))))
    assert(symbols.isValue(FiniteSet(Seq(IntegerLiteral(1)), IntegerType())))
    assert(symbols.isValue(FiniteMap(Seq(IntegerLiteral(1) -> BooleanLiteral(true)), BooleanLiteral(false), IntegerType(), BooleanType())))
    assert(symbols.isValue(ADT(nilID, Seq(IntegerType()), Seq())))
    assert(!symbols.isValue(x))
    assert(!symbols.isValue(IntegerLiteral(1) + IntegerLiteral(2)))
    assert(!symbols.isValue(FiniteSet(Seq(x), IntegerType())))
    assert(!symbols.isValueOfType(IntegerLiteral(1), BooleanType()))
  }

  test("Constructors") {
    val t = Variable.fresh("t", TupleType(Seq(IntegerType(), IntegerType())))
    val l = Variable.fresh("l", ADTType(listID, Seq(IntegerType())))
    assert(symbols.tupleSelect(Tuple(Seq(x, y)), 2, true) == y)
    assert(symbols.tupleSelect(t, 1, true) == TupleSelect(t, 1))
    assert(symbols.tupleSelect(x, 1, false) == x)
    assert(symbols.let(x.toVal, y, x) == Let(x.toVal, y, x))
    assert(symbols.let(x.toVal, y, z) == z)
    assert(symbols.let(x.toVal, y + z, x * x) == Let(x.toVal, y + z, x * x))
    assert(symbols.ifExpr(BooleanLiteral(true), x, y) == x)
    assert(symbols.ifExpr(BooleanLiteral(false), x, y) == y)
    assert(symbols.ifExpr(p, x, x) == x)
    assert(symbols.ifExpr(p, BooleanLiteral(true), BooleanLiteral(false)) == p)
    assert(symbols.ifExpr(p, BooleanLiteral(false), BooleanLiteral(true)) == Not(p))
    assert(symbols.ifExpr(p, BooleanLiteral(true), q) == Or(p, q))
    assert(symbols.ifExpr(p, q, BooleanLiteral(false)) == And(p, q))
    assert(symbols.application(Lambda(Seq(x.toVal), x + x), Seq(y)) == y + y)
    assert(symbols.adtSelector(ADT(consID, Seq(IntegerType()), Seq(x, l)), headID) == x)
    assert(symbols.adtSelector(l, headID) == ADTSelector(l, headID))
    assert(symbols.isCons(l, nilID) == IsConstructor(l, nilID))
    assert(symbols.forall(Seq(x.toVal), BooleanLiteral(true)) == BooleanLiteral(true))
    assert(symbols.forall(Seq(x.toVal, y.toVal), x > z) == Forall(Seq(x.toVal), x > z))
  }

  test("Paths") {
    val v = Variable.fresh("v", IntegerType())
    val path = Path(v.toVal -> (x + y)) `withCond` (v > IntegerLiteral(0)) `withCond` p
    assert(path.bindings == Seq(v.toVal -> (x + y)))
    assert(path.conditions == Seq(v > IntegerLiteral(0), p))
    assert(path.closed == Seq(v.toVal))
    assert(path.open.isEmpty)
    assert(path.bound == Seq(v.toVal))
    assert(path.freeVariables == Set(x, y, p))
    assert(path.unboundVariables == Set(x, y, p))
    assert(path.isBound(v) && !path.isBound(x))
    assert(path.freeOf(v + z) == Set(z, x, y, p))
    assert(path.unboundOf(v + z) == Set(z, x, y, p))
    assert(!path.isEmpty)
    assert(Path.empty.isEmpty)
    assert(Path(x.toVal).isEmpty)

    assert(path.toClause == Let(v.toVal, x + y, And(v > IntegerLiteral(0), p)))
    assert(path.fullClause == Let(v.toVal, x + y, And(v > IntegerLiteral(0), And(p, BooleanLiteral(true)))))
    assert(path.implies(q) == Let(v.toVal, x + y, Implies(And(v > IntegerLiteral(0), p), q)))
    assert(path.and(q) == Let(v.toVal, x + y, And(Seq(v > IntegerLiteral(0), p, q))))
    assert(path.negate.bindings == path.bindings)
    assert(path.negate.conditions == Seq(Or(v <= IntegerLiteral(0), Not(p))))

    // conjunctions and negated disjunctions are split into their conditions
    assert((Path.empty `withCond` And(p, q)).conditions == Seq(p, q))
    assert((Path.empty `withCond` Not(Or(p, q))).conditions == Seq(Not(p), Not(q)))
    assert((Path.empty `withCond` BooleanLiteral(true)).isEmpty)
    assert(Path(Let(v.toVal, x, Equals(v, y))) == (Path(v.toVal -> x) `withCond` Equals(v, y)))
    assert(Path(BooleanLiteral(true)).isEmpty)
    assert(Path(Seq(p, BooleanLiteral(true), q)).conditions == Seq(p, q))

    // a variable can't be bound once the path uses it
    assertThrows[AssertionError](path `withBinding` (x.toVal -> y))
    assertThrows[AssertionError](path `withBound` y.toVal)

    val opened = Path(z.toVal) `withCond` (z > x)
    assert(opened.open == Seq(z.toVal))
    assert(opened.freeVariables == Set(x))
    assert(opened.unboundVariables == Set(z, x))
    assert((opened -- Set(z.toVal)).open.isEmpty)
    assert((path -- Set(v.toVal)).bindings.isEmpty)

    assert(path.merge(opened).conditions == Seq(v > IntegerLiteral(0), p, z > x))
    assert(path.merge(path) == path)
    assert(Path.empty.merge(Seq(path, opened)) == path.merge(opened))
    assert(path.map(identity, e => exprOps.replaceFromSymbols(Map(p -> q), e)).conditions == Seq(v > IntegerLiteral(0), q))

    val T = TypeParameter.fresh("T")
    val tv = Variable.fresh("tv", T)
    val tw = Variable.fresh("tw", T)
    val generic = Path(tv.toVal -> tw) `withCond` Equals(tv, tw)
    val instantiated = generic.instantiate(Map(T -> IntegerType()))
    assert(instantiated.bindings.head._1.getType == IntegerType())
    assert(instantiated.conditions.map(_.getType) == Seq(BooleanType()))

    assert(path.asString(using PrinterOptions()) == path.fullClause.asString(using PrinterOptions()))
    assert(path.toString == path.fullClause.asString(using PrinterOptions()))
    assert(Path.fold[Int](0, (_, _, n) => n + 10, (_, n) => n + 1)(opened.elements) == 1)
  }
}
