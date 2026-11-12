/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package evaluators

import org.scalatest.funsuite.AnyFunSuite

/** Semantics of the recursive evaluator that follow SMT-LIB where the evaluators of other projects, tested
  * through [[EvaluatorSuite]], differ: Stainless's evaluators take the amount of `Int32` and `Int64` shifts
  * modulo the width, as the JVM does, and its code generator shifts unsigned bitvectors logically. Its code
  * generator also still divides integers toward zero and takes the remainder of bit-vectors for `Modulo`.
  * Also checks that the recursive evaluator stops when its context is interrupted, which the other
  * evaluators don't, that it rejects ill-typed expressions with an evaluator error, and that it reports the
  * failures of well-typed ones (division by zero, failed assumptions, exhausted steps) as runtime errors.
  */
class RecursiveEvaluatorSuite extends AnyFunSuite {
  import inox.trees._

  val ctx = TestContext.empty
  val program = InoxProgram(NoSymbols)
  val evaluator = RecursiveEvaluator(program, ctx)

  def eval(expr: Expr): Expr = evaluator.eval(expr) match {
    case EvaluationResults.Successful(res) => res
    case other => fail(s"Evaluation of '$expr' failed with $other")
  }

  test("Evaluation stops when its context is interrupted") {
    val interruptible = ctx.copy(interruptManager = new utils.InterruptManager(ctx.reporter))
    val e = RecursiveEvaluator(program, interruptible)
    val sum = Plus(IntegerLiteral(1), IntegerLiteral(1))
    assert(e.eval(sum).result == Some(IntegerLiteral(2)))
    interruptible.interruptManager.interrupt()
    assert(e.eval(sum) == EvaluationResults.RuntimeError("Evaluation interrupted"))
    interruptible.interruptManager.reset()
    assert(e.eval(sum).result == Some(IntegerLiteral(2)))
  }

  test("Int32 and Int64 shifts by out-of-range amounts") {
    // The amount is read as an unsigned value: shifting by the width or more, or by a negative amount, vacates
    // all the bits, which `>>` fills with the most significant bit
    assert(eval(BVShiftLeft(Int32Literal(1), Int32Literal(32)))                     === Int32Literal(0))
    assert(eval(BVShiftLeft(Int32Literal(1), Int32Literal(33)))                     === Int32Literal(0))
    assert(eval(BVShiftLeft(Int32Literal(1), Int32Literal(-1)))                     === Int32Literal(0))
    assert(eval(BVShiftLeft(Int32Literal(Int.MinValue), Int32Literal(-1)))          === Int32Literal(0))
    assert(eval(BVLShiftRight(Int32Literal(Int.MinValue), Int32Literal(32)))        === Int32Literal(0))
    assert(eval(BVLShiftRight(Int32Literal(Int.MinValue), Int32Literal(33)))        === Int32Literal(0))
    assert(eval(BVLShiftRight(Int32Literal(-1), Int32Literal(-1)))                  === Int32Literal(0))
    assert(eval(BVAShiftRight(Int32Literal(Int.MinValue), Int32Literal(32)))        === Int32Literal(-1))
    assert(eval(BVAShiftRight(Int32Literal(Int.MinValue), Int32Literal(33)))        === Int32Literal(-1))
    assert(eval(BVAShiftRight(Int32Literal(Int.MinValue), Int32Literal(-1)))        === Int32Literal(-1))
    assert(eval(BVAShiftRight(Int32Literal(Int.MaxValue), Int32Literal(32)))        === Int32Literal(0))
    assert(eval(BVAShiftRight(Int32Literal(Int.MaxValue), Int32Literal(-1)))        === Int32Literal(0))

    assert(eval(BVShiftLeft(Int64Literal(1), Int64Literal(64)))                     === Int64Literal(0))
    assert(eval(BVShiftLeft(Int64Literal(1), Int64Literal(65)))                     === Int64Literal(0))
    assert(eval(BVShiftLeft(Int64Literal(1), Int64Literal(1L << 32)))               === Int64Literal(0))
    assert(eval(BVShiftLeft(Int64Literal(1), Int64Literal(-1)))                     === Int64Literal(0))
    assert(eval(BVLShiftRight(Int64Literal(-1), Int64Literal(64)))                  === Int64Literal(0))
    assert(eval(BVAShiftRight(Int64Literal(Long.MinValue), Int64Literal(64)))       === Int64Literal(-1))
    assert(eval(BVAShiftRight(Int64Literal(Long.MinValue), Int64Literal(1L << 32))) === Int64Literal(-1))
  }

  test("`>>` on unsigned bitvectors fills with the most significant bit, as SMT-LIB `bvashr`") {
    def ubvl(x: BigInt) = BVLiteral(false, x, 11)
    assert(eval(BVAShiftRight(ubvl(1024), ubvl(1)))  === ubvl(1536))
    assert(eval(BVAShiftRight(ubvl(1024), ubvl(11))) === ubvl(2047))
    assert(eval(BVAShiftRight(ubvl(1023), ubvl(11))) === ubvl(0))
  }

  test("Substrings out of bounds give an empty or truncated string, as SMT-LIB `str.substr`") {
    // Stainless's code generator calls `String.substring`, which throws on these
    def sub(s: String, from: BigInt, to: BigInt) =
      SubString(StringLiteral(s), IntegerLiteral(from), IntegerLiteral(to))

    assert(eval(sub("abc", 1, 2))  === StringLiteral("b"))
    assert(eval(sub("abc", 0, 3))  === StringLiteral("abc"))
    assert(eval(sub("abc", 1, 10)) === StringLiteral("bc"))
    assert(eval(sub("abc", -1, 2)) === StringLiteral(""))
    assert(eval(sub("abc", 3, 4))  === StringLiteral(""))
    assert(eval(sub("abc", 5, 6))  === StringLiteral(""))
    assert(eval(sub("abc", 2, 1))  === StringLiteral(""))
    assert(eval(sub("abc", 1, 1))  === StringLiteral(""))
    assert(eval(sub("", 0, 1))     === StringLiteral(""))
    assert(eval(sub("abc", BigInt(Long.MaxValue) * 4, BigInt(Long.MaxValue) * 5)) === StringLiteral(""))
    assert(eval(sub("abc", 1, BigInt(Long.MaxValue) * 4)) === StringLiteral("bc"))
  }

  test("BigInt Division, Remainder and Modulo with negative operands, as SMT-LIB `div` and `mod`") {
    // `x == y * (x / y) + (x mod y)` with `0 <= x mod y < |y|`, and the remainder is `mod`
    for ((x, y, q, r) <- Seq((-1, 3, -1, 2), (-1, -3, 1, 2), (-7, 2, -4, 1), (7, -2, -3, 1), (-7, -2, 4, 1))) {
      assert(eval(Division(IntegerLiteral(x), IntegerLiteral(y)))  === IntegerLiteral(q))
      assert(eval(Remainder(IntegerLiteral(x), IntegerLiteral(y))) === IntegerLiteral(r))
      assert(eval(Modulo(IntegerLiteral(x), IntegerLiteral(y)))    === IntegerLiteral(r))
    }
  }

  test("BitVector Modulo has the sign of the divisor, as SMT-LIB `bvsmod`") {
    assert(eval(Modulo(Int32Literal(-1), Int32Literal(-3))) === Int32Literal(-1))
    assert(eval(Modulo(Int32Literal(1), Int32Literal(-3)))  === Int32Literal(-2))
  }

  val t = BooleanLiteral(true)
  val i = IntegerLiteral(1)
  val c = CharLiteral('c')
  val s = StringLiteral("s")
  val set = FiniteSet(Seq(i), IntegerType())
  val bag = FiniteBag(Seq(i -> IntegerLiteral(2)), IntegerType())
  val map = FiniteMap(Seq(i -> i), IntegerLiteral(0), IntegerType(), IntegerType())
  val bv = Int32Literal(1)

  private def evaluatorError(e: Expr): Unit = evaluator.eval(e) match {
    case EvaluationResults.EvaluatorError(_) =>
    case res => fail(s"Unexpected result $res for $e")
  }

  private def runtimeError(e: Expr): Unit = evaluator.eval(e) match {
    case EvaluationResults.RuntimeError(_) =>
    case res => fail(s"Unexpected result $res for $e")
  }

  test("Ill-typed booleans and conditionals") {
    evaluatorError(IfExpr(i, i, i))
    evaluatorError(And(i, t))
    evaluatorError(Or(i, t))
    evaluatorError(Not(i))
    evaluatorError(Implies(i, t))
    evaluatorError(Application(i, Seq(i)))
    evaluatorError(Variable.fresh("free", IntegerType()))
  }

  test("Ill-typed arithmetic") {
    for (op <- Seq[(Expr, Expr) => Expr](Plus.apply, Minus.apply, Times.apply, Division.apply, Remainder.apply,
        Modulo.apply, LessThan.apply, GreaterThan.apply, LessEquals.apply, GreaterEquals.apply))
      evaluatorError(op(t, t))
    evaluatorError(UMinus(t))
    for (op <- Seq[(Expr, Expr) => Expr](BVAnd.apply, BVOr.apply, BVXor.apply, BVShiftLeft.apply,
        BVAShiftRight.apply, BVLShiftRight.apply))
      evaluatorError(op(i, i))
    evaluatorError(BVNot(i))
    evaluatorError(BVWideningCast(i, Int64Type()))
    evaluatorError(BVNarrowingCast(i, Int8Type()))
    evaluatorError(BVUnsignedToSigned(i))
    evaluatorError(BVSignedToUnsigned(i))
    evaluatorError(BVToInt(i))
    evaluatorError(IntToBV(32, true, t))
  }

  test("Ill-typed strings") {
    evaluatorError(StringConcat(i, s))
    evaluatorError(StringLength(i))
    evaluatorError(SubString(i, i, i))
  }

  test("Ill-typed collections") {
    for (op <- Seq[(Expr, Expr) => Expr](SetUnion.apply, SetIntersection.apply, SetDifference.apply, SubsetOf.apply))
      evaluatorError(op(i, set))
    evaluatorError(SetAdd(i, i))
    evaluatorError(ElementOfSet(i, i))
    evaluatorError(MapMerge(i, map, map))
    for (op <- Seq[(Expr, Expr) => Expr](BagUnion.apply, BagIntersection.apply, BagDifference.apply))
      evaluatorError(op(i, bag))
    evaluatorError(BagAdd(i, i))
    evaluatorError(MultiplicityInBag(i, i))
    evaluatorError(MapApply(i, i))
    evaluatorError(MapUpdated(i, i, i))
  }

  test("Well-typed set and character operations") {
    assert(evaluator.eval(SubsetOf(set, set)).result == Some(t))
    assert(evaluator.eval(SubsetOf(set, FiniteSet(Seq(), IntegerType()))).result == Some(BooleanLiteral(false)))
    assert(evaluator.eval(GreaterThan(c, CharLiteral('a'))).result == Some(t))
    assert(evaluator.eval(LessEquals(c, CharLiteral('a'))).result == Some(BooleanLiteral(false)))
    assert(evaluator.eval(GreaterEquals(c, c)).result == Some(t))
  }

  test("Runtime errors") {
    runtimeError(Division(IntegerLiteral(1), IntegerLiteral(0)))
    runtimeError(Division(FractionLiteral(1, 2), FractionLiteral(0, 1)))
    runtimeError(Remainder(IntegerLiteral(1), IntegerLiteral(0)))
    runtimeError(Modulo(IntegerLiteral(1), IntegerLiteral(0)))
    runtimeError(Assume(BooleanLiteral(false), i))
    runtimeError(Error(IntegerType(), "boom"))
  }

  test("Function calls are bounded by the maximal number of steps") {
    val fid = FreshIdentifier("loop")
    val x = ValDef.fresh("x", IntegerType())
    val loop = new FunDef(fid, Seq(), Seq(x), IntegerType(), FunctionInvocation(fid, Seq(), Seq(x.toVariable)), Seq())
    val p = InoxProgram(NoSymbols.withFunctions(Seq(loop)))
    val e = RecursiveEvaluator(p, TestContext(Options(Seq(optMaxCalls(10)))))
    e.eval(FunctionInvocation(fid, Seq(), Seq(i))) match {
      case EvaluationResults.RuntimeError(msg) => assert(msg.contains("Exceeded number of allocated methods calls"))
      case res => fail(s"Unexpected result $res")
    }
  }

  test("Lambdas whose lifted subexpressions don't hold or fail evaluate, and only fail when applied") {
    val x = ValDef.fresh("x", IntegerType())
    val k = ValDef.fresh("k", IntegerType())
    val (zero, one, two, ten) = (IntegerLiteral(0), IntegerLiteral(1), IntegerLiteral(2), IntegerLiteral(10))
    // `10 / k` is lifted out of the body under `k > 0`, or unconditionally under `--assume-checked`
    def guarded(kv: Expr) = Let(k, kv,
      Lambda(Seq(x), IfExpr(GreaterThan(k.toVariable, zero), Plus(x.toVariable, Division(ten, k.toVariable)), x.toVariable)))
    val unguarded = Lambda(Seq(x), Plus(x.toVariable, Division(one, zero)))

    for (assumeChecked <- Seq(false, true)) {
      val ev = RecursiveEvaluator(program, ctx.withOpts(solvers.optAssumeChecked(assumeChecked)))
      def evalOk(expr: Expr): Expr = ev.eval(expr) match {
        case EvaluationResults.Successful(res) => res
        case other => fail(s"Evaluation of '$expr' failed with $other under assume-checked=$assumeChecked")
      }
      evalOk(guarded(zero))
      evalOk(unguarded)
      assert(evalOk(Application(guarded(zero), Seq(IntegerLiteral(7)))) == IntegerLiteral(7))
      assert(evalOk(Application(guarded(two), Seq(IntegerLiteral(7)))) == IntegerLiteral(12))
      assert(evalOk(Equals(guarded(zero), guarded(zero))) == BooleanLiteral(true))
      assert(ev.eval(Application(unguarded, Seq(one))) == EvaluationResults.RuntimeError("Division by 0."))
    }
  }
}
