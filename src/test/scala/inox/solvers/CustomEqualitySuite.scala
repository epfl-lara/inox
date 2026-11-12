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
      case Seq(x) =>
        val r = "r" :: IntegerType()
        exprOps.uninterpretedCall("pick", Seq(), Seq(x.asInstanceOf[Variable].toVal),
          RefinementType(r, r.toVariable > MultiplicityInBag(E(BigInt(1)), x)))
    })
  }

  val listID = FreshIdentifier("List")
  val consID = FreshIdentifier("Cons")
  val nilID = FreshIdentifier("Nil")
  val headID = FreshIdentifier("head")
  val tailID = FreshIdentifier("tail")
  val listSort = mkSort(listID)("A") { case Seq(aT) => Seq(
    (nilID, Seq()),
    (consID, Seq(ValDef(headID, aT), ValDef(tailID, T(listID)(aT)))))
  }

  /** Whether `x` is an element of `l`, which compares elements with the equality of `A`. */
  val containsID = FreshIdentifier("contains")
  val containsFd = mkFunDef(containsID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT), "x" :: aT), BooleanType(), {
      case Seq(l, x) =>
        (l `is` consID) && (Equals(l.getField(headID), x) || E(containsID)(aT)(l.getField(tailID), x))
    })
  }

  /** The sum of the multiplicities of 1 in the bags of `l`. */
  val totalID = FreshIdentifier("total")
  val totalFd = mkFunDef(totalID)() { _ => (
    Seq("l" :: T(listID)(BagType(IntegerType()))), IntegerType(), {
      case Seq(l) =>
        if_ (l `is` consID) {
          MultiplicityInBag(E(BigInt(1)), l.getField(headID)) + E(totalID)(l.getField(tailID))
        } else_ {
          E(BigInt(0))
        }
    })
  }

  override protected def symbols: Symbols =
    NoSymbols.withSorts(Seq(boxSort, listSort)).withFunctions(Seq(countFd, pickFd, containsFd, totalFd))
  given Symbols = symbols

  override protected def solverInfos = super.solverInfos.map { info =>
    // Princess unrolls the quantified bag equality slowly: even "Bag equality" takes ~20s,
    // and nested equalities take minutes, so only its real (and set) equalities are tested here.
    if (info.name == "princess") info.copy(
      unsupported = info.unsupported + Bags,
      knownIssues = info.knownIssues +
        ("Real equality under quantifiers" -> "a single satisfiability check doesn't terminate"))
    // cvc4 and cvc5 share the `BagEncoder`, and bag equalities are slow on cvc4, so only cvc5 runs these.
    else if (info.name == "smt-cvc4") info.copy(unsupported = info.unsupported + Bags)
    else if (info.name == "smt-cvc5") info.copy(knownIssues = info.knownIssues +
      ("Models of lambdas over bags" -> ("the model of a lambda is an application of the lambdas that structure " +
        "normalization lifts out of its body (here, the `Node` of a bag union), so it isn't structurally equal " +
        "to the lambda and model checking rejects it")))
    else info
  }

  // Models are checked by evaluation below, so that invalid models aren't hidden as `Unknown`.
  // Closures are compared structurally, up to the custom equality of their captured values, which
  // needs the intensional semantics of function equality.
  override protected def options = Seq(optCheckModels(false),
    unrolling.optFunctionEquality(unrolling.FunctionEquality.Intensional))

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

  test("Bag arguments of functions with a refined uninterpreted call", Bags) { ctx =>
    valid(ctx, Equals(FunctionInvocation(pickID, Seq(), Seq(ab)), FunctionInvocation(pickID, Seq(), Seq(ba))))
  }

  test("Bag arguments of free functions", Bags, Functions) { ctx =>
    val g = Variable.fresh("g", FunctionType(Seq(BT), IntegerType()))
    valid(ctx, Equals(Application(g, Seq(ab)), Application(g, Seq(ba))))
    satisfiable(ctx, And(
      Equals(Application(g, Seq(BagUnion(bag(2), bag(1)))), one),
      Not(Equals(Application(g, Seq(bag(3))), one))))
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

  def nil(tpe: Type): Expr = ADT(nilID, Seq(tpe), Seq())
  def cons(h: Expr, t: Expr): Expr = ADT(consID, Seq(h.getType), Seq(h, t))
  def list(es: Expr*): Expr = es.foldRight(nil(es.head.getType))(cons)
  def contains(l: Expr, x: Expr): Expr = FunctionInvocation(containsID, Seq(x.getType), Seq(l, x))
  def total(l: Expr): Expr = FunctionInvocation(totalID, Seq(), Seq(l))
  def count(e: Expr): Expr = MultiplicityInBag(one, e)

  test("Bags within recursive ADTs", Bags, ADTs) { ctx =>
    valid(ctx, Equals(list(a, ab), list(a, ba)))
    valid(ctx, Not(Equals(list(ab), list(ab, ab))))
    val l = Variable.fresh("l", T(listID)(BT))
    val m = Variable.fresh("m", T(listID)(BT))
    valid(ctx, Implies(And(Equals(l, cons(ab, m)), Equals(m, list(a))), Equals(l, list(ba, a))))
    satisfiable(ctx, andJoin(Seq(Equals(l, m), IsConstructor(l, consID), Equals(count(ADTSelector(l, headID)), two))))
    satisfiable(ctx, And(Not(Equals(l, m)), Equals(total(l), total(m))))
  }

  test("Bags within recursive ADTs in function calls", Bags, ADTs) { ctx =>
    valid(ctx, Equals(total(list(ab, a)), total(list(ba, a))))
    val l = Variable.fresh("l", T(listID)(BT))
    valid(ctx, Implies(Equals(l, list(ab, b)), Equals(total(l), Plus(count(a), Times(two, count(b))))))
  }

  test("Bag equality in generic functions", Bags, ADTs) { ctx =>
    valid(ctx, contains(list(ab), ba))
    valid(ctx, Implies(contains(list(a), b), Equals(count(a), count(b))))
  }

  test("Real equality in generic functions", Reals, ADTs) { ctx =>
    valid(ctx, contains(list(half, Plus(r, r)), Times(twice, r)))
    satisfiable(ctx, And(contains(list(Plus(r, r)), r), Equals(Times(r, r), r)))
    valid(ctx, Equals(list(Plus(r, half)), list(Plus(half, r))))
  }

  test("Bag equality under quantifiers", Bags, Functions, Quantifiers) { ctx =>
    val g = Variable.fresh("g", FunctionType(Seq(IntegerType()), BT))
    val h = Variable.fresh("h", FunctionType(Seq(IntegerType()), BT))
    val x = Variable.fresh("x", IntegerType())
    valid(ctx, Implies(
      Forall(Seq(x.toVal), Equals(Application(g, Seq(x)), Application(h, Seq(x)))),
      Equals(BagUnion(Application(g, Seq(one)), a), BagUnion(a, Application(h, Seq(one))))))
    valid(ctx, Implies(
      Forall(Seq(x.toVal), Equals(tup(Application(g, Seq(x))), tup(ab))),
      Equals(tup(Application(g, Seq(two))), tup(ba))))
  }

  test("Quantifiers over bags", Bags, Functions, Quantifiers) { ctx =>
    val f = Variable.fresh("f", FunctionType(Seq(BT), IntegerType()))
    val s = Variable.fresh("s", BT)
    valid(ctx, Implies(
      Forall(Seq(s.toVal), Equals(Application(f, Seq(s)), count(s))),
      Equals(Application(f, Seq(ab)), Application(f, Seq(ba)))))
    valid(ctx, Implies(
      Forall(Seq(s.toVal), Equals(Application(f, Seq(s)), count(s))),
      Equals(Application(f, Seq(ab)), count(ba))))
    val F = Variable.fresh("F", FunctionType(Seq(TupleType(Seq(BT, IntegerType()))), IntegerType()))
    val p = Variable.fresh("p", TupleType(Seq(BT, IntegerType())))
    valid(ctx, Implies(
      Forall(Seq(p.toVal), Equals(Application(F, Seq(p)), count(TupleSelect(p, 1)))),
      Equals(Application(F, Seq(tup(ab))), Application(F, Seq(tup(ba))))))
  }

  test("Quantifiers over ADTs of bags", Bags, ADTs, Functions, Quantifiers) { ctx =>
    val f = Variable.fresh("f", FunctionType(Seq(T(boxID)()), IntegerType()))
    val y = Variable.fresh("y", T(boxID)())
    valid(ctx, Implies(
      Forall(Seq(y.toVal), GreaterThan(Application(f, Seq(y)), Application(f, Seq(box(bag()))))),
      GreaterThan(Application(f, Seq(box(ab))), Application(f, Seq(box(BagUnion(bag(), bag())))))))
  }

  test("Higher-order functions over bags", Bags, Functions) { ctx =>
    val H = Variable.fresh("H", FunctionType(Seq(FunctionType(Seq(IntegerType()), BT)), IntegerType()))
    valid(ctx, Equals(Application(H, Seq(const(ab))), Application(H, Seq(const(ba)))))
    val k = Variable.fresh("k", FunctionType(Seq(BT), FunctionType(Seq(BT), IntegerType())))
    valid(ctx, Equals(Application(Application(k, Seq(ab)), Seq(a)), Application(Application(k, Seq(ba)), Seq(a))))
    val g = Variable.fresh("g", FunctionType(Seq(IntegerType()), BT))
    val f = Variable.fresh("f", FunctionType(Seq(BT), IntegerType()))
    valid(ctx, Equals(
      Application(f, Seq(BagUnion(Application(g, Seq(one)), a))),
      Application(f, Seq(BagUnion(a, Application(g, Seq(one)))))))
  }

  test("Lambdas over bags", Bags, Functions) { ctx =>
    val s = Variable.fresh("s", BT)
    val lam = Lambda(Seq(s.toVal), count(BagUnion(s, a)))
    valid(ctx, Equals(Application(lam, Seq(ab)), Application(lam, Seq(ba))))
    val f = Variable.fresh("f", FunctionType(Seq(BT), IntegerType()))
    valid(ctx, Implies(Equals(f, lam), Equals(Application(f, Seq(ab)), Application(f, Seq(ba)))))
    val p = Variable.fresh("p", TupleType(Seq(BT, IntegerType())))
    val tl = Lambda(Seq(p.toVal), count(TupleSelect(p, 1)))
    valid(ctx, Equals(Application(tl, Seq(tup(ab))), Application(tl, Seq(tup(ba)))))
  }

  test("Models of lambdas over bags", Bags, Functions) { ctx =>
    val s = Variable.fresh("s", BT)
    val lam = Lambda(Seq(s.toVal), count(BagUnion(s, a)))
    val f = Variable.fresh("f", FunctionType(Seq(BT), IntegerType()))
    satisfiable(ctx, And(Equals(f, lam), Equals(Application(f, Seq(ab)), two)))
  }

  test("Reals in higher-order functions", Reals, Functions) { ctx =>
    val k = Variable.fresh("k", FunctionType(Seq(RealType()), FunctionType(Seq(RealType()), IntegerType())))
    valid(ctx, Equals(Application(Application(k, Seq(Plus(r, r))), Seq(r)), Application(Application(k, Seq(Times(twice, r))), Seq(r))))
  }

  test("Real equality under quantifiers", Reals, Functions, Quantifiers) { ctx =>
    val g = Variable.fresh("g", FunctionType(Seq(IntegerType()), TupleType(Seq(RealType(), IntegerType()))))
    val x = Variable.fresh("x", IntegerType())
    notDisproved(ctx, Implies(
      Forall(Seq(x.toVal), Equals(Application(g, Seq(x)), tup(Plus(r, r)))),
      Equals(Application(g, Seq(one)), tup(Times(twice, r)))))
  }

  /** Random formulas over bags nested within tuples, ADTs and closures.
    *
    * Z3 encodes bags natively, without custom equalities, so its answers are a reference for the
    * solvers that use the `BagEncoder`: they must never contradict it, and their models must
    * evaluate to true.
    */
  test("Random bag formulas agree with Z3", Bags, ADTs, Functions) { ctx =>
    val reference = "smt-z3"
    val name = ctx.options.findOptionOrDefault(optSelectedSolvers).head
    if (name == "smt-cvc5" && SolverFactory.hasZ3) {
      val rnd = new scala.util.Random(42)
      val c = Variable.fresh("c", BT)
      def pick[A](as: A*): A = as(rnd.nextInt(as.size))
      def bagTerm(depth: Int): Expr =
        if (depth == 0 || rnd.nextInt(3) == 0) pick(a, b, c, bag(), bag(1), bag(1, 2))
        else pick(0, 1, 2) match {
          case 0 => BagUnion(bagTerm(depth - 1), bagTerm(depth - 1))
          case 1 => BagAdd(bagTerm(depth - 1), pick(one, two))
          case 2 => pick(a, b, c)
        }
      def wrap(k: Int, e: Expr): Expr = k match {
        case 0 => e
        case 1 => tup(e)
        case 2 => box(e)
        case 3 => list(e, a)
        case 4 => const(e)
      }
      def atom: Expr = pick(0, 0, 1, 2) match {
        case 0 =>
          val k = rnd.nextInt(5)
          Equals(wrap(k, bagTerm(2)), wrap(k, bagTerm(2)))
        case 1 => Equals(MultiplicityInBag(pick(one, two), bagTerm(2)), pick(E(BigInt(0)), one, two))
        case 2 => GreaterEquals(count(bagTerm(2)), count(bagTerm(2)))
      }
      def literal: Expr = if (rnd.nextBoolean()) atom else Not(atom)

      def solve(solverName: String, e: Expr) = {
        val sctx = contextFor(solverName).withOpts(optCheckModels(false))
        SimpleSolverAPI(program.getSolver(sctx).withTimeout(scala.concurrent.duration.Duration(2, "s"))).solveSAT(e)
      }

      var decided = 0
      val formulas = (1 to 12).map { i =>
        rnd.setSeed(42L * i)
        andJoin(Seq.fill(2 + rnd.nextInt(2))(literal))
      }
      for (e <- formulas) {
        val res = solve(name, e)
        val ref = solve(reference, e)
        res match {
          case SatWithModel(model) => checkModel(ctx, e, model)
          case _ =>
        }
        (res, ref) match {
          case (Unsat, SatWithModel(model)) =>
            fail(s"${e.asString} was found unsatisfiable, but $reference found ${model.vars}")
          case (SatWithModel(model), Unsat) =>
            fail(s"$reference found ${e.asString} unsatisfiable, but got ${model.vars}")
          case (Unsat | SatWithModel(_), Unsat | SatWithModel(_)) => decided += 1
          case _ =>
        }
      }
      info(s"$decided of ${formulas.size} formulas decided by both solvers")
    }
  }
}
