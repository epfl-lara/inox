/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** Uninterpreted calls return arbitrary values of their types, which models give. */
class UninterpretedCallSuite extends UnrollingTestSuite {
  import trees._
  import dsl._
  import SolverResponses._

  val idU = FreshIdentifier("idU")
  val greaterU = FreshIdentifier("greaterU")
  val sumU = FreshIdentifier("sumU")
  val boundedU = FreshIdentifier("boundedU")
  val positiveU = FreshIdentifier("positiveU")
  val pickU = FreshIdentifier("pickU")
  val sameU = FreshIdentifier("sameU")

  val anyT = FunctionType(Seq(IntegerType()), IntegerType())

  /** `(p: Int) => {r: Int | r > p}` */
  val greaterT = {
    val p = ValDef.fresh("p", IntegerType())
    val r = ValDef.fresh("r", IntegerType())
    PiType(Seq(p), RefinementType(r, r.toVariable > p.toVariable))
  }

  /** `(a: Int, b: Int) => {r: Int | r > a + b}` */
  val sumT = {
    val a = ValDef.fresh("a", IntegerType())
    val b = ValDef.fresh("b", IntegerType())
    val r = ValDef.fresh("r", IntegerType())
    PiType(Seq(a, b), RefinementType(r, r.toVariable > a.toVariable + b.toVariable))
  }

  /** `(lo: Int, hi: {v: Int | v > lo}) => {r: Int | lo < r && r <= hi}` */
  val boundedT = {
    val lo = ValDef.fresh("lo", IntegerType())
    val v = ValDef.fresh("v", IntegerType())
    val hi = "hi" :: RefinementType(v, v.toVariable > lo.toVariable)
    val r = ValDef.fresh("r", IntegerType())
    PiType(Seq(lo, hi), RefinementType(r, lo.toVariable < r.toVariable && r.toVariable <= hi.toVariable))
  }

  /** `() => {r: Int | r > 0}` */
  val positiveT = {
    val r = ValDef.fresh("r", IntegerType())
    FunctionType(Seq(), RefinementType(r, r.toVariable > E(BigInt(0))))
  }

  /** `(p: T) => {r: T | r == p}` */
  def sameT(tp: Type) = {
    val p = ValDef.fresh("p", tp)
    val r = ValDef.fresh("r", tp)
    PiType(Seq(p), RefinementType(r, r.toVariable === p.toVariable))
  }

  def greaterCall(arg: Expr) = UninterpretedCall(greaterU, Seq(), Seq(arg), greaterT)

  // A function whose result is any integer
  val any = mkFunDef(FreshIdentifier("any"))()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => UninterpretedCall(idU, Seq(), Seq(x), anyT) }))

  // A function whose result is refined over its argument
  val greater = mkFunDef(FreshIdentifier("greater"))()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => greaterCall(x) }))

  // A function whose uninterpreted call takes an argument that isn't a variable
  val greaterTwice = mkFunDef(FreshIdentifier("greaterTwice"))()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => greaterCall(x * E(BigInt(2))) }))

  // A generic function whose result is any value
  val pick = mkFunDef(FreshIdentifier("pick"))("T")(tps => (
    Seq("x" :: tps.head), tps.head, { case Seq(x) =>
      UninterpretedCall(pickU, tps, Seq(x), FunctionType(Seq(tps.head), tps.head)) }))

  // A generic function whose result is refined over its argument
  val same = mkFunDef(FreshIdentifier("same"))("T")(tps => (
    Seq("x" :: tps.head), tps.head, { case Seq(x) => UninterpretedCall(sameU, tps, Seq(x), sameT(tps.head)) }))

  // A function that calls one with an uninterpreted call
  val incAny = mkFunDef(FreshIdentifier("incAny"))()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => any(x) + E(BigInt(1)) }))

  val symbols = NoSymbols.withFunctions(Seq(any, greater, greaterTwice, pick, same, incAny))
  val program = InoxProgram(symbols)

  /** The model of `clause`, after checking that it satisfies the clause. */
  def modelOf(clause: Expr)(using Context): program.Model = {
    val res = SimpleSolverAPI(program.getSolver).solveSAT(clause)
    val SatWithModel(model) = res: @unchecked
    val evRes = program.getEvaluator.eval(clause, model)
    assert(evRes.result == Some(BooleanLiteral(true)), s"$evRes in $model")
    model
  }

  test("results of uninterpreted calls are arbitrary") {
    val model = modelOf(any(IntegerLiteral(0)) === IntegerLiteral(1))
    assert(model.chooses contains (idU -> Seq()), model)
  }

  test("uninterpreted calls are functional") {
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    assert(SimpleSolverAPI(program.getSolver).solveSAT(x === y && Not(any(x) === any(y))).isUNSAT)
  }

  test("uninterpreted calls in queries") {
    val x = Variable.fresh("x", IntegerType())
    val call = UninterpretedCall(idU, Seq(), Seq(x), anyT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(call === any(x))).isUNSAT)
    modelOf(call === IntegerLiteral(3) && any(IntegerLiteral(0)) === IntegerLiteral(1))
  }

  test("uninterpreted calls across push and pop") { ctx ?=>
    // The free function of an uninterpreted call outlives the scope in which it first appears
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    val solver = program.getSolver.getNewSolver()
    try {
      solver.push()
      solver.assertCnstr(greaterCall(x) === y)
      assert(solver.check(Model).isSAT)
      solver.pop()
      solver.assertCnstr(x === y && greaterCall(x) <= y)
      assert(solver.check(Model).isUNSAT)
      solver.reset()
      solver.assertCnstr(any(x) === y && Not(any(x) === y))
      assert(solver.check(Model).isUNSAT)
      solver.reset()
      solver.assertCnstr(greaterCall(x) === y)
      solver.check(Model) match {
        case SatWithModel(model) =>
          val evRes = program.getEvaluator.eval(greaterCall(x) === y, model)
          assert(evRes.result == Some(BooleanLiteral(true)), s"$evRes in $model")
        case res => fail(s"Expected a model, got $res")
      }
    } finally solver.free()
  }

  test("results of uninterpreted calls lie in their types") {
    val x = Variable.fresh("x", IntegerType())
    assert(SimpleSolverAPI(program.getSolver).solveSAT(greater(x) <= x).isUNSAT)
    modelOf(greater(IntegerLiteral(0)) === IntegerLiteral(5))
  }

  test("results of uninterpreted calls lie in their types at arguments that aren't variables") {
    val x = Variable.fresh("x", IntegerType())
    assert(SimpleSolverAPI(program.getSolver).solveSAT(greaterTwice(x) <= x * E(BigInt(2))).isUNSAT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(greaterCall(x + E(BigInt(1))) <= x + E(BigInt(1))).isUNSAT)
    // The result is only bound by its argument, not by the arguments of other calls
    modelOf(greaterTwice(x) === x * E(BigInt(2)) + E(BigInt(1)))
    modelOf(greaterCall(x + E(BigInt(1))) === x + E(BigInt(2)) && greaterCall(x) === x + E(BigInt(1)))
    modelOf(greaterTwice(IntegerLiteral(3)) === IntegerLiteral(7))
  }

  test("each call binds the parameters to its own arguments") {
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    assert(SimpleSolverAPI(program.getSolver).solveSAT(
      greaterCall(x) <= x || greaterCall(y) <= y || greater(y) <= y).isUNSAT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(
      x === y + E(BigInt(10)) && greaterCall(y) <= x).isSAT)
    // Equal arguments, through distinct expressions, still give equal results
    assert(SimpleSolverAPI(program.getSolver).solveSAT(
      Not(greaterCall(x + E(BigInt(1))) === greaterCall(E(BigInt(1)) + x))).isUNSAT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(
      Not(greaterTwice(x) === greaterCall(x + x))).isUNSAT)
  }

  test("results may depend on several parameters") {
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    def sum(a: Expr, b: Expr) = UninterpretedCall(sumU, Seq(), Seq(a, b), sumT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(sum(x, y) <= x + y).isUNSAT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(sum(y, x * E(BigInt(3))) <= y + x * E(BigInt(3))).isUNSAT)
    modelOf(sum(x, y) === x + y + E(BigInt(1)) && sum(y, x) === x + y + E(BigInt(1)))
  }

  test("parameter types may depend on earlier parameters") {
    val x = Variable.fresh("x", IntegerType())
    def bounded(lo: Expr, hi: Expr) = UninterpretedCall(boundedU, Seq(), Seq(lo, hi), boundedT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(
      Not(bounded(x, x + E(BigInt(1))) === x + E(BigInt(1)))).isUNSAT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(
      bounded(x, x + E(BigInt(5))) <= x || bounded(x, x + E(BigInt(5))) > x + E(BigInt(5))).isUNSAT)
    modelOf(bounded(IntegerLiteral(0), IntegerLiteral(5)) === IntegerLiteral(3))
  }

  test("results of nullary calls lie in their types") {
    val call = UninterpretedCall(positiveU, Seq(), Seq(), positiveT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(call <= E(BigInt(0))).isUNSAT)
    val model = modelOf(call === E(BigInt(4)))
    assert(model.chooses contains (positiveU -> Seq()), model)
  }

  test("uninterpreted calls whose results don't lie in their types aren't satisfiable") {
    val x = Variable.fresh("x", IntegerType())
    assert(SimpleSolverAPI(program.getSolver).solveSAT(greater(x) === x).isUNSAT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(greaterTwice(IntegerLiteral(2)) === IntegerLiteral(4)).isUNSAT)
  }

  test("uninterpreted calls through other functions") {
    val x = Variable.fresh("x", IntegerType())
    modelOf(incAny(IntegerLiteral(0)) === IntegerLiteral(5))
    modelOf(incAny(x) === IntegerLiteral(5) && any(IntegerLiteral(3)) === IntegerLiteral(2))
  }

  test("generic uninterpreted calls are defined at each instantiation") { ctx ?=>
    // Princess can't give the values of its functions at generic or datatype results
    assume(ctx.options.findOptionOrDefault(optSelectedSolvers) != Set("princess"))
    val tp = TypeParameter.fresh("A")
    val a = Variable.fresh("a", tp)
    val model = modelOf(Not(pick(tp)(a) === a) && pick(IntegerType())(IntegerLiteral(0)) === IntegerLiteral(1))
    assert(model.chooses contains (pickU -> Seq(tp)), model)
    assert(model.chooses contains (pickU -> Seq(IntegerType())), model)
  }

  test("generic results are refined at each instantiation") { ctx ?=>
    val tp = TypeParameter.fresh("A")
    val a = Variable.fresh("a", tp)
    val x = Variable.fresh("x", IntegerType())
    assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(same(tp)(a) === a)).isUNSAT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(same(IntegerType())(x + E(BigInt(1))) === x + E(BigInt(1)))).isUNSAT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(same(BooleanType())(E(true)))).isUNSAT)
  }

  test("models of refined uninterpreted functions evaluate within their types") {
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    val model = modelOf(greaterTwice(x) > E(BigInt(10)) && greater(y) < E(BigInt(0)))
    val evaluator = program.getEvaluator
    // At the arguments of the calls that the solver unrolled, the results lie in their types
    for ((v, call) <- Seq(x * E(BigInt(2)) -> greaterTwice(x), y -> greater(y))) {
      assert(evaluator.eval(call > v, model).result == Some(BooleanLiteral(true)), s"$call in $model")
    }
  }

  test("evaluating an uninterpreted call outside the model is an error") { ctx ?=>
    assert(program.getEvaluator.eval(incAny(IntegerLiteral(0))).result.isEmpty)
    assert(program.getEvaluator.eval(greater(IntegerLiteral(3))).result.isEmpty)
  }

  test("quantifiers hold in the model of the uninterpreted functions they call") { ctx ?=>
    val x = ValDef.fresh("x", IntegerType())
    val positive = Forall(Seq(x), incAny(x.toVariable) > E(BigInt(1)))
    def anyIs(n: BigInt) = inox.Model(program)(Map.empty, Map((idU, Seq()) -> Lambda(Seq(x), E(n))))
    val evaluator = program.getEvaluator
    assert(evaluator.eval(positive, anyIs(1)).result == Some(BooleanLiteral(true)))
    assert(evaluator.eval(positive, anyIs(0)).result == Some(BooleanLiteral(false)))
    // The interpretation applies to arguments that aren't variables
    val shifted = Forall(Seq(x), incAny(x.toVariable + E(BigInt(1))) > E(BigInt(1)))
    assert(evaluator.eval(shifted, anyIs(1)).result == Some(BooleanLiteral(true)))
    assert(evaluator.eval(shifted, anyIs(0)).result == Some(BooleanLiteral(false)))
  }

  test("quantifiers hold in the model of refined uninterpreted functions") { ctx ?=>
    val x = ValDef.fresh("x", IntegerType())
    val p = ValDef.fresh("p", IntegerType())
    def greaterIs(n: BigInt) =
      inox.Model(program)(Map.empty, Map((greaterU, Seq()) -> Lambda(Seq(p), p.toVariable + E(n))))
    val bound = Forall(Seq(x), greaterTwice(x.toVariable) <= x.toVariable * E(BigInt(2)) + E(BigInt(3)))
    val evaluator = program.getEvaluator
    assert(evaluator.eval(bound, greaterIs(3)).result == Some(BooleanLiteral(true)))
    assert(evaluator.eval(bound, greaterIs(4)).result == Some(BooleanLiteral(false)))
  }

  test("quantifiers hold in recursive models of uninterpreted functions") { ctx ?=>
    // `idU(n) = if (n <= 0) 0 else idU(n - 1) + 1`, which only unfolding the interpretation as
    // often as the quantifier needs establishes
    val n = ValDef.fresh("n", IntegerType())
    def call(arg: Expr) = UninterpretedCall(idU, Seq(), Seq(arg), anyT)
    val recursive = inox.Model(program)(Map.empty, Map((idU, Seq()) -> Lambda(Seq(n),
      if_ (n.toVariable <= E(BigInt(0))) { E(BigInt(0)) } else_ { call(n.toVariable - E(BigInt(1))) + E(BigInt(1)) })))
    val x = ValDef.fresh("x", IntegerType())
    val evaluator = program.getEvaluator
    def bounded(body: Expr) = Forall(Seq(x), (E(BigInt(0)) <= x.toVariable && x.toVariable <= E(BigInt(3))) ==> body)
    assert(evaluator.eval(bounded(any(x.toVariable) === x.toVariable), recursive).result == Some(BooleanLiteral(true)))
    assert(evaluator.eval(bounded(any(x.toVariable) === E(BigInt(2))), recursive).result == Some(BooleanLiteral(false)))
    // Through other functions too
    assert(evaluator.eval(bounded(incAny(x.toVariable) === x.toVariable + E(BigInt(1))), recursive).result == Some(BooleanLiteral(true)))

    // The solvers that operate under the model unfold the interpretation as a function
    val y = Variable.fresh("y", IntegerType())
    val solver = SolverFactory.getFromName("smt-z3", force = true)(program, ctx, Some(recursive))(
      transformers.ProgramEncoder.empty(program))(using program.getSemantics).getNewSolver()
    try {
      solver.assertCnstr(E(BigInt(0)) <= y && y <= E(BigInt(5)) && Not(any(y) === y))
      assert(solver.check(Simple).isUNSAT)
    } finally solver.free()
  }

  test("closures that make distinct uninterpreted calls are distinct") { ctx ?=>
    val f1 = FreshIdentifier("f1")
    val f2 = FreshIdentifier("f2")
    def closure(f: Identifier) = Lambda(Seq(), UninterpretedCall(f, Seq(), Seq(), FunctionType(Seq(), IntegerType())))
    val model = inox.Model(program)(Map.empty, Map((f1, Seq()) -> Lambda(Seq(), E(BigInt(1))), (f2, Seq()) -> Lambda(Seq(), E(BigInt(1)))))
    val evaluator = program.getEvaluator
    assert(evaluator.eval(Application(closure(f1), Seq()), model).result == Some(IntegerLiteral(1)))
    assert(evaluator.eval(closure(f1) === closure(f2), model).result == Some(BooleanLiteral(false)))
    assert(evaluator.eval(closure(f1) === closure(f1), model).result == Some(BooleanLiteral(true)))
  }
}
