/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Equalities on types whose encoding has a custom equality (`HasADTEquality`): bags on the
  * solvers that use the `BagEncoder`, and reals and sets on Princess.
  *
  * Structurally different encodings of the same value (e.g. `a ∪ b` and `b ∪ a`) must be equal
  * wherever they appear: nested within tuples and ADTs, as arguments of functions, within
  * closures, and so on. Models are checked by evaluation, so a spurious counterexample fails
  * the test instead of returning `Unknown`.
  */
class CustomEqualitySuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses._

  val boxID = FreshIdentifier("Box")
  val boxCons = FreshIdentifier("Box")
  val boxSort = mkSort(boxID)() { _ =>
    Seq((boxCons, Seq(ValDef(FreshIdentifier("b"), BagType(IntegerType())))))
  }

  val countID = FreshIdentifier("count")
  val countFd = mkFunDef(countID)() { _ => (
    Seq("x" :: BagType(IntegerType())), IntegerType(), {
      case Seq(x) => MultiplicityInBag(E(BigInt(1)), x)
    })
  }

  val pickID = FreshIdentifier("pick")
  val pickFd = mkFunDef(pickID)() { _ => (
    Seq("x" :: BagType(IntegerType())), IntegerType(), {
      case Seq(x) => choose("r" :: IntegerType())(r => r > MultiplicityInBag(E(BigInt(1)), x))
    })
  }

  override protected def symbols: Symbols =
    NoSymbols.withSorts(Seq(boxSort)).withFunctions(Seq(countFd, pickFd))
  given Symbols = symbols

  // Models are checked by evaluation below, so that invalid models aren't hidden as `Unknown`.
  override protected def options = Seq(optCheckModels(false))

  /** Checks that `e` is valid. */
  def valid(ctx: Context, e: Expr): Unit = solver(ctx).solveSAT(Not(e)) match {
    case Unsat => // OK
    case SatWithModel(model) => fail(s"Found a counterexample to valid formula ${e.asString}: ${model.vars}")
    case res => fail(s"Couldn't prove ${e.asString}, got $res")
  }

  /** Checks that `e` has a model, and that it is valid.
    *
    * Models that satisfy a positive custom equality (e.g. bag equality, which is quantified)
    * can't be certified by quantifier instantiation alone, so we let the solver check its
    * models by evaluation, as with `--check-models`.
    */
  def satisfiable(ctx: Context, e: Expr): Unit = solver(ctx.withOpts(optCheckModels(true))).solveSAT(e) match {
    case SatWithModel(model) => checkModel(ctx, e, model)
    case res => fail(s"Couldn't find a model for ${e.asString}, got $res")
  }

  /** Checks that the solver neither proves `e` nor finds an invalid model for it.
    *
    * Used where a solver may legitimately give up, e.g. on unsupported features.
    */
  def notRefuted(ctx: Context, e: Expr): Unit = solver(ctx).solveSAT(e) match {
    case Unsat => fail(s"Satisfiable formula ${e.asString} was found unsatisfiable")
    case SatWithModel(model) => checkModel(ctx, e, model)
    case _ => // OK
  }

  /** Checks that the solver neither finds a counterexample to valid `e` (nor an invalid model). */
  def notDisproved(ctx: Context, e: Expr): Unit = solver(ctx).solveSAT(Not(e)) match {
    case SatWithModel(model) => fail(s"Found a counterexample to valid formula ${e.asString}: ${model.vars}")
    case _ => // OK
  }

  def checkModel(ctx: Context, e: Expr, model: inox.Model): Unit = {
    val vars = model.vars.asInstanceOf[Map[ValDef, Expr]].map { case (vd, v) => vd.toVariable -> v }
    program.getEvaluator(ctx).eval(exprOps.replaceFromSymbols(vars, e)).result match {
      case Some(BooleanLiteral(true)) => // OK
      case res => fail(s"Invalid model ${vars.map(p => p._1.asString + " -> " + p._2.asString).mkString(", ")} for ${e.asString}: evaluates to $res")
    }
  }

  val BT = BagType(IntegerType())
  val a = Variable.fresh("a", BT)
  val b = Variable.fresh("b", BT)
  val one = E(BigInt(1))
  val two = E(BigInt(2))
  val ab = BagUnion(a, b)
  val ba = BagUnion(b, a)
  def bag(ks: Int*): Expr = FiniteBag(ks.map(k => E(BigInt(k)) -> one), IntegerType())
  def tup(e: Expr): Expr = Tuple(Seq(e, one))
  def box(e: Expr): Expr = ADT(boxCons, Seq(), Seq(e))
  /** A constant function whose closure holds the value of `e`. */
  def const(e: Expr): Expr = {
    val v = Variable.fresh("v", e.getType)
    Let(v.toVal, e, \("x" :: IntegerType())(_ => v))
  }

  test("Bag equality", Bags) { ctx =>
    valid(ctx, Equals(ab, ba))
  }

  test("Bag equality within tuples", Bags) { ctx =>
    valid(ctx, Equals(tup(ab), tup(ba)))
    satisfiable(ctx, And(Equals(tup(a), tup(b)), Equals(MultiplicityInBag(one, a), one)))
  }

  test("Bag equality within ADTs", Bags, ADTs) { ctx =>
    valid(ctx, Equals(box(ab), box(ba)))
    valid(ctx, Implies(Equals(box(a), box(b)), Equals(MultiplicityInBag(one, a), MultiplicityInBag(one, b))))
    satisfiable(ctx, And(Equals(box(a), box(b)), Equals(MultiplicityInBag(one, a), one)))
  }

  test("Bag arguments of functions", Bags) { ctx =>
    valid(ctx, Equals(FunctionInvocation(countID, Seq(), Seq(ab)), FunctionInvocation(countID, Seq(), Seq(ba))))
  }

  test("Bag arguments of functions with a choose", Bags) { ctx =>
    valid(ctx, Equals(FunctionInvocation(pickID, Seq(), Seq(ab)), FunctionInvocation(pickID, Seq(), Seq(ba))))
  }

  test("Bag arguments of free functions", Bags, Functions) { ctx =>
    val g = Variable.fresh("g", FunctionType(Seq(BT), IntegerType()))
    valid(ctx, Equals(Application(g, Seq(ab)), Application(g, Seq(ba))))
    satisfiable(ctx, andJoin(Seq(
      Equals(Application(g, Seq(bag(1, 2))), one),
      Equals(Application(g, Seq(BagUnion(bag(2), bag(1)))), Application(g, Seq(a))),
      Not(Equals(Application(g, Seq(bag(3))), one)))))
  }

  test("Bag results of free functions", Bags, Functions) { ctx =>
    val g = Variable.fresh("g", FunctionType(Seq(IntegerType()), BT))
    valid(ctx, Equals(BagUnion(Application(g, Seq(one)), a), BagUnion(a, Application(g, Seq(one)))))
  }

  test("Bags within closures", Bags, Functions) { ctx =>
    valid(ctx, Equals(const(ab), const(ba)))
    satisfiable(ctx, Not(Equals(const(a), const(b))))
    satisfiable(ctx, And(Equals(const(a), const(b)), Equals(MultiplicityInBag(one, a), one)))
  }

  test("Bags within maps", Bags, Maps) { ctx =>
    valid(ctx, Equals(MapApply(FiniteMap(Seq(one -> ab), bag(), IntegerType(), BT), one), ba))
  }

  test("Bags as set elements and map keys", Bags, Sets, Maps) { ctx =>
    // Solvers compare set elements and map keys structurally, so these are rejected
    // (or solved natively), but never answered wrongly.
    notDisproved(ctx, ElementOfSet(ba, FiniteSet(Seq(ab), BT)))
    notDisproved(ctx, Equals(MapApply(FiniteMap(Seq(ab -> one), two, BT, IntegerType()), ba), one))
    notRefuted(ctx, And(Equals(FiniteSet(Seq(ab), BT), FiniteSet(Seq(ba), BT)), Not(Equals(a, b))))
    notRefuted(ctx, And(
      Equals(FiniteMap(Seq(ab -> one), two, BT, IntegerType()), FiniteMap(Seq(ba -> one), two, BT, IntegerType())),
      Not(Equals(a, b))))
    notDisproved(ctx, Equals(FiniteMap(Seq(one -> ab), bag(), IntegerType(), BT), FiniteMap(Seq(one -> ba), bag(), IntegerType(), BT)))
  }

  val r = Variable.fresh("r", RealType())
  val half = FractionLiteral(1, 2)
  val twice = FractionLiteral(2, 1)

  test("Real equality within tuples", Reals) { ctx =>
    valid(ctx, Equals(tup(Plus(r, r)), tup(Times(twice, r))))
    satisfiable(ctx, And(Equals(tup(Plus(r, r)), tup(Times(twice, r))), Equals(r, half)))
  }

  test("Reals within closures", Reals, Functions) { ctx =>
    valid(ctx, Equals(const(Plus(r, r)), const(Times(twice, r))))
    satisfiable(ctx, And(Equals(const(Plus(r, r)), const(Times(twice, r))), Equals(r, half)))
  }

  test("Real arguments of free functions", Reals, Functions) { ctx =>
    val h = Variable.fresh("h", FunctionType(Seq(RealType()), IntegerType()))
    valid(ctx, Equals(Application(h, Seq(Plus(r, r))), Application(h, Seq(Times(twice, r)))))
  }

  test("Set equality within tuples", Sets) { ctx =>
    val s = Variable.fresh("s", SetType(IntegerType()))
    val t = Variable.fresh("t", SetType(IntegerType()))
    valid(ctx, Equals(tup(SetUnion(s, t)), tup(SetUnion(t, s))))
  }
}
