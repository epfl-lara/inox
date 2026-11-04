/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

import SolverResponses._

/** Regression suite for type unrolling and quantifier instantiation.
  *
  * Values of refinement, Sigma, Pi and ADT types are constrained by type templates (see
  * [[TypeTemplates]] and `TemplateGenerator.mkTypeClauses`). The tests below check these
  * constraints through their observable effect on queries, in the places where they matter:
  *
  *  - quantifier domains, where a type check may be false and must then simply disable the
  *    instantiation (positive polarity) or the counterexample (negative polarity);
  *  - predicates that may falsify their path (`assume`, `choose`, and calls into either);
  *  - ADT invariants, with the free and the contract generators;
  *  - type parameters and higher-order values, including closure captures;
  *  - the same type checked both inside and outside of a quantifier domain in one query.
  *
  * Most tests come in pairs: a valid query, and an invalid one that a too strong (or unsound)
  * encoding would prove. The `instantiates` queries check positive quantifier domains:
  * `(forall (w: T) => g(w) == 1) ==> g(v) == 1` is valid iff `v` belongs to `T`.
  * The `holds` queries check negative quantifier domains: `forall (w: T) => p(w)`.
  */
class TypeUnrollingSuite extends UnrollingTestSuite with DatastructureUtils {
  import trees.{given, _}
  import dsl.{given, _}

  // Model checks are set per query, see `solverFor`.
  override protected def optionMatrix = UnrollingTestSuite.combinations(
    UnrollingTestSuite.both(optFeelingLucky),
    UnrollingTestSuite.both(optUnrollAssumptions),
    UnrollingTestSuite.both(optAssumeChecked),
    Seq(optModelFinding(0), optModelFinding(1))
  )

  def int(i: Int): Expr = IntegerLiteral(i)
  val I = IntegerType()

  // {y: BigInt | y > 0}
  val pos = refinement("y" :: I)(_ > int(0))
  // {y: BigInt | y != 0}
  val nonZero = refinement("y" :: I)(_ !== int(0))

  /* ---- Functions whose clauses may falsify their path ---- */

  // pre(a) = { assume(a != 0); true }, similarly to a Stainless `require`
  val preID = FreshIdentifier("pre")
  val pre = mkFunDef(preID)() { _ => (
    Seq("a" :: I), BooleanType(), { case Seq(a) => Assume(a !== int(0), E(true)) })
  }

  // pre2(a) = pre(a), the assumption is reached transitively
  val pre2ID = FreshIdentifier("pre2")
  val pre2 = mkFunDef(pre2ID)() { _ => (
    Seq("a" :: I), BooleanType(), { case Seq(a) => E(preID)(a) })
  }

  // chooseNonZero(a) = choose((r: Boolean) => r && a != 0), which has no value for a == 0
  val chooseNonZeroID = FreshIdentifier("chooseNonZero")
  val chooseNonZero = mkFunDef(chooseNonZeroID)() { _ => (
    Seq("a" :: I), BooleanType(), { case Seq(a) => choose("r" :: BooleanType())(r => r && (a !== int(0))) })
  }

  /* ---- ADTs with refined fields ---- */

  // case class Box(bv: {y | y > 0}), non-inductive
  val boxID = FreshIdentifier("Box")
  val boxConsID = FreshIdentifier("Box")
  val bv = FreshIdentifier("bv")
  val boxSort = mkSort(boxID)() { _ => Seq((boxConsID, Seq(ValDef(bv, pos)))) }
  val Box = T(boxID)()

  // Tree = Leaf | Node(left: Tree, value: {y | y > 0}, right: Tree), inductive with two recursive fields
  val treeID = FreshIdentifier("Tree")
  val leafID = FreshIdentifier("Leaf")
  val nodeID = FreshIdentifier("Node")
  val left = FreshIdentifier("left")
  val nodeValue = FreshIdentifier("value")
  val right = FreshIdentifier("right")
  val treeSort = mkSort(treeID)() { _ => Seq(
    (leafID, Seq()),
    (nodeID, Seq(ValDef(left, T(treeID)()), ValDef(nodeValue, pos), ValDef(right, T(treeID)())))
  )}
  val Tree = T(treeID)()

  /* ---- ADT invariants ---- */

  val isPositiveID = FreshIdentifier("isPositive")
  val isPositive = mkFunDef(isPositiveID)() { _ => (
    Seq("x" :: I), BooleanType(), { case Seq(x) => x > int(0) })
  }

  // case class Pos(pv: BigInt) { require(isPositive(pv)) }, non-recursive, invariant calls a function
  val posID = FreshIdentifier("Pos")
  val posConsID = FreshIdentifier("Pos")
  val pv = FreshIdentifier("pv")
  val posInvID = FreshIdentifier("posInv")
  val posInv = mkFunDef(posInvID)() { _ => (
    Seq("p" :: T(posID)()), BooleanType(), { case Seq(p) => E(isPositiveID)(p.getField(pv)) })
  }
  val posSort = mkSort(posID, HasADTInvariant(posInvID))() { _ => Seq((posConsID, Seq(ValDef(pv, I)))) }
  val Pos = T(posID)()

  // PList = PNil | PCons(ph: BigInt, pt: PList), with invariant `l is PCons ==> l.ph > 0`, recursive
  val plistID = FreshIdentifier("PList")
  val pnilID = FreshIdentifier("PNil")
  val pconsID = FreshIdentifier("PCons")
  val ph = FreshIdentifier("ph")
  val pt = FreshIdentifier("pt")
  val plistInvID = FreshIdentifier("plistInv")
  val plistInv = mkFunDef(plistInvID)() { _ => (
    Seq("l" :: T(plistID)()), BooleanType(), { case Seq(l) => (l `is` pconsID) ==> (l.getField(ph) > int(0)) })
  }
  val plistSort = mkSort(plistID, HasADTInvariant(plistInvID))() { _ => Seq(
    (pnilID, Seq()),
    (pconsID, Seq(ValDef(ph, I), ValDef(pt, T(plistID)())))
  )}
  val PList = T(plistID)()

  // case class Wrapper(wl: List[BigInt]) { require(allPos(wl)) }, invariant calls a recursive function
  val allPosID = FreshIdentifier("allPos")
  val allPos = mkFunDef(allPosID)() { _ => (
    Seq("l" :: T(listID)(I)), BooleanType(), { case Seq(l) =>
      if_ (l `is` consID) {
        (l.getField(head) > int(0)) && E(allPosID)(l.getField(tail))
      } else_ {
        E(true)
      }
    })
  }
  val wrapperID = FreshIdentifier("Wrapper")
  val wrapperConsID = FreshIdentifier("Wrapper")
  val wl = FreshIdentifier("wl")
  val wrapperInvID = FreshIdentifier("wrapperInv")
  val wrapperInv = mkFunDef(wrapperInvID)() { _ => (
    Seq("w" :: T(wrapperID)()), BooleanType(), { case Seq(w) => E(allPosID)(w.getField(wl)) })
  }
  val wrapperSort = mkSort(wrapperID, HasADTInvariant(wrapperInvID))() { _ => Seq(
    (wrapperConsID, Seq(ValDef(wl, T(listID)(I))))
  )}
  val Wrapper = T(wrapperID)()

  /* ---- Higher-order values ---- */

  // case class FunBox(fn: BigInt => BigInt)
  val funBoxID = FreshIdentifier("FunBox")
  val funBoxConsID = FreshIdentifier("FunBox")
  val fn = FreshIdentifier("fn")
  val funBoxSort = mkSort(funBoxID)() { _ => Seq((funBoxConsID, Seq(ValDef(fn, I =>: I)))) }
  val FunBox = T(funBoxID)()

  // case class PosFun(pf: BigInt => {y | y > 0})
  val posFunID = FreshIdentifier("PosFun")
  val posFunConsID = FreshIdentifier("PosFun")
  val pf = FreshIdentifier("pf")
  val posFunSort = mkSort(posFunID)() { _ => Seq((posFunConsID, Seq(ValDef(pf, I =>: pos)))) }
  val PosFun = T(posFunID)()

  // def first[A](f: BigInt => A): A = f(0)
  val firstID = FreshIdentifier("first")
  val first = mkFunDef(firstID)("A") { case Seq(aT) => (
    Seq("f" :: (I =>: aT)), aT, { case Seq(f) => f(int(0)) })
  }

  val symbols = baseSymbols
    .withFunctions(Seq(pre, pre2, chooseNonZero, isPositive, posInv, plistInv, allPos, wrapperInv, first))
    .withSorts(Seq(boxSort, treeSort, posSort, plistSort, wrapperSort, funBoxSort, posFunSort))
  given Symbols = symbols

  val program = InoxProgram(symbols)

  /* ---- Helpers ---- */

  def list(tpe: Type)(elems: Expr*): Expr =
    elems.foldRight(ADT(nilID, Seq(tpe), Seq()): Expr)((h, t) => ADT(consID, Seq(tpe), Seq(h, t)))
  def ints(elems: Int*): Expr = list(I)(elems.map(int)*)

  def box(i: Int): Expr = ADT(boxConsID, Seq(), Seq(int(i)))
  val leaf: Expr = ADT(leafID, Seq(), Seq())
  def node(l: Expr, v: Int, r: Expr): Expr = ADT(nodeID, Seq(), Seq(l, int(v), r))

  /** `(forall (w: tpe) => g(w) == 1) ==> g(v) == 1`, valid iff `v` belongs to `tpe`. */
  def instantiates(tpe: Type, v: Expr): Expr = {
    val g = Variable.fresh("g", FunctionType(Seq(tpe.getType), I))
    val w = Variable.fresh("w", tpe)
    Forall(Seq(w.toVal), g(w) === int(1)) ==> (g(v) === int(1))
  }

  /** `forall (w: tpe) => p(w)` */
  def holds(tpe: Type)(p: Variable => Expr): Expr = {
    val w = Variable.fresh("w", tpe)
    Forall(Seq(w.toVal), p(w))
  }

  private def containsQuantifiers(e: Expr): Boolean = {
    def local(e: Expr) = exprOps.exists { case _: Forall => true case _ => false }(e)
    local(e) || exprOps.functionCallsOf(e).exists { fi =>
      (symbols.transitiveCallees(fi.id) + fi.id).exists(id => local(symbols.getFunction(id).fullBody))
    }
  }

  // Countermodels of quantified formulas can't be checked by evaluation,
  // so models are only checked for queries without quantifiers.
  private def solverFor(e: Expr)(using ctx: Context) =
    SimpleSolverAPI(program.getSolver(ctx.withOpts(optCheckModels(!containsQuantifiers(e)))))

  private def show(e: Expr)(using ctx: Context): String =
    e.asString(using PrinterOptions.fromContext(ctx, Some(symbols)))

  def assertValid(e: Expr, clue: String = "")(using Context): Unit = {
    val res = solverFor(e).solveVALID(e)
    assert(res == Some(true), s"$clue: expected ${show(e)} to be valid, but got $res")
  }

  def assertInvalid(e: Expr, clue: String = "")(using Context): Unit = {
    val res = solverFor(e).solveVALID(e)
    assert(res == Some(false), s"$clue: expected ${show(e)} to be invalid, but got $res")
  }

  def assertSat(e: Expr, clue: String = "")(using Context): Unit = {
    val res = solverFor(e).solveSAT(e)
    assert(res.isSAT, s"$clue: expected ${show(e)} to be satisfiable, but got $res")
  }

  def assertUnsat(e: Expr, clue: String = "")(using Context): Unit = {
    val res = solverFor(e).solveSAT(e)
    assert(res.isUNSAT, s"$clue: expected ${show(e)} to be unsatisfiable, but got $res")
  }

  /* ==== 1. Quantifier domains ==== */

  test("domain: refinement") {
    assertValid(instantiates(pos, int(1)), "in domain")
    assertInvalid(instantiates(pos, int(0)), "outside domain")
    assertValid(holds(pos)(_ > int(0)), "holds")
    assertInvalid(holds(pos)(_ > int(1)), "doesn't hold")
  }

  test("domain: nested refinement") {
    // {x: {y | y > 0} | x < 10}
    val small = refinement("x" :: pos)(_ < int(10))
    assertValid(instantiates(small, int(5)), "in domain")
    assertInvalid(instantiates(small, int(0)), "outside base type")
    assertInvalid(instantiates(small, int(10)), "outside predicate")
    assertValid(holds(small)(x => x > int(0) && x < int(10)), "holds")
    assertInvalid(holds(small)(_ < int(9)), "doesn't hold")
  }

  test("domain: Sigma") {
    // (a: BigInt, {b: BigInt | b > a})
    val incr = sigma("a" :: I)(a => refinement("b" :: I)(_ > a))
    assertValid(instantiates(incr, E(int(1), int(2))), "in domain")
    assertInvalid(instantiates(incr, E(int(2), int(1))), "outside domain")
    assertValid(holds(incr)(p => p._ts2 > p._ts1), "holds")
    assertInvalid(holds(incr)(p => p._ts2 > p._ts1 + int(1)), "doesn't hold")
  }

  test("domain: Sigma with refined parameter") {
    // (a: {y | y > 0}, {b: BigInt | b > a})
    val incr = sigma("a" :: pos)(a => refinement("b" :: I)(_ > a))
    assertValid(instantiates(incr, E(int(1), int(2))), "in domain")
    assertInvalid(instantiates(incr, E(int(-1), int(0))), "parameter outside domain")
    assertInvalid(instantiates(incr, E(int(2), int(1))), "last component outside domain")
    assertValid(holds(incr)(p => p._ts2 > int(1)), "holds")
    assertInvalid(holds(incr)(p => p._ts2 > int(2)), "doesn't hold")
  }

  test("domain: Pi") {
    // (a: BigInt) => {r: BigInt | r > a}
    val incr = pi("a" :: I)(a => refinement("r" :: I)(_ > a))
    assertValid(holds(incr)(h => h(int(0)) > int(0)), "holds")
    assertInvalid(holds(incr)(h => h(int(0)) > int(1)), "doesn't hold")
    assertValid(holds(incr)(h => h(h(int(0))) > int(1)), "holds (nested applications)")
  }

  test("domain: Pi with refined parameter") {
    // (a: {y | y > 0}) => {r: BigInt | r > a}
    val incr = pi("a" :: pos)(a => refinement("r" :: I)(_ > a))
    assertValid(holds(incr)(h => h(int(1)) > int(1)), "holds")
    assertInvalid(holds(incr)(h => h(int(1)) > int(2)), "doesn't hold")
  }

  test("domain: non-inductive ADT") {
    assertValid(instantiates(Box, box(1)), "in domain")
    assertInvalid(instantiates(Box, box(0)), "outside domain")
    assertValid(holds(Box)(b => b.getField(bv) > int(0)), "holds")
    assertInvalid(holds(Box)(b => b.getField(bv) > int(1)), "doesn't hold")
  }

  test("domain: inductive ADT") {
    val posList = T(listID)(pos)
    assertValid(instantiates(posList, ints()), "fieldless constructor")
    assertValid(instantiates(posList, ints(1)), "depth 1")
    assertValid(instantiates(posList, ints(1, 2)), "depth 2")
    assertInvalid(instantiates(posList, ints(0)), "depth 1 outside domain")
    assertInvalid(instantiates(posList, ints(1, 0)), "depth 2 outside domain")
    assertValid(holds(posList)(l => (l `is` consID) ==> (l.getField(head) > int(0))), "holds at depth 1")
    assertValid(holds(posList)(l =>
      ((l `is` consID) && (l.getField(tail) `is` consID)) ==> (l.getField(tail).getField(head) > int(0))),
      "holds at depth 2")
    assertInvalid(holds(posList)(l =>
      ((l `is` consID) && (l.getField(tail) `is` consID)) ==> (l.getField(tail).getField(head) > int(1))),
      "doesn't hold at depth 2")
  }

  test("domain: inductive ADT with several recursive fields") {
    assertValid(instantiates(Tree, leaf), "fieldless constructor")
    assertValid(instantiates(Tree, node(leaf, 1, node(leaf, 2, leaf))), "depth 2")
    assertInvalid(instantiates(Tree, node(leaf, 1, node(leaf, 0, leaf))), "right subtree outside domain")
    assertInvalid(instantiates(Tree, node(node(leaf, 0, leaf), 1, leaf)), "left subtree outside domain")
    assertValid(holds(Tree)(t =>
      ((t `is` nodeID) && (t.getField(right) `is` nodeID)) ==> (t.getField(right).getField(nodeValue) > int(0))),
      "holds at depth 2")
    assertInvalid(holds(Tree)(t =>
      ((t `is` nodeID) && (t.getField(left) `is` nodeID)) ==> (t.getField(left).getField(nodeValue) > int(1))),
      "doesn't hold at depth 2")
  }

  // The type checks of sets, maps and bags decompose them one element at a time, which only
  // terminates for finite values. Their domain tests are therefore limited to finite values,
  // see the known issues below for the other cases.

  test("domain: set with refined elements") {
    val posSet = SetType(pos)
    assertValid(instantiates(posSet, FiniteSet(Seq(), I)), "empty")
    assertInvalid(instantiates(posSet, FiniteSet(Seq(int(1), int(0)), I)), "outside domain")
    val x = Variable.fresh("x", I)
    assertInvalid(holds(posSet)(s => Forall(Seq(x.toVal), ElementOfSet(x, s) ==> (x > int(1)))), "doesn't hold")
    val s = Variable.fresh("s", posSet)
    assertValid((s === FiniteSet(Seq(x), I)) ==> (x > int(0)), "free variable")
    assertInvalid((s === FiniteSet(Seq(x), I)) ==> (x > int(1)), "free variable")
  }

  test("domain: map with refined values") {
    val posMap = MapType(I, pos)
    assertInvalid(instantiates(posMap, FiniteMap(Seq(int(0) -> int(0)), int(1), I, I)), "value outside domain")
    assertInvalid(instantiates(posMap, FiniteMap(Seq(int(0) -> int(2)), int(0), I, I)), "default outside domain")
    val k = Variable.fresh("k", I)
    assertInvalid(holds(posMap)(m => Forall(Seq(k.toVal), MapApply(m, k) > int(1))), "doesn't hold")
    val m = Variable.fresh("m", posMap)
    assertInvalid(MapApply(m, k) > int(1), "free variable")
  }

  test("domain: bag with refined elements") {
    val posBag = BagType(pos)
    assertValid(instantiates(posBag, FiniteBag(Seq(), I)), "empty")
    assertInvalid(instantiates(posBag, FiniteBag(Seq(int(1) -> int(1), int(0) -> int(1)), I)), "outside domain")
    val x = Variable.fresh("x", I)
    assertInvalid(holds(posBag)(b => Forall(Seq(x.toVal), (MultiplicityInBag(x, b) > int(0)) ==> (x > int(1)))), "doesn't hold")
    val b = Variable.fresh("b", posBag)
    assertInvalid((b === FiniteBag(Seq(x -> int(1)), I)) ==> (x > int(1)), "free variable")
  }

  /* ==== 2. Predicates that may falsify their path ==== */

  // Each predicate only holds (only makes its assumptions) within the base type {y | y != 0}.
  // Outside of the base type, the type check must be false without falsifying the path.
  val guardedTypes: Seq[(String, Type)] = Seq(
    "assume" -> refinement("x" :: nonZero)(x => Assume(x !== int(0), E(true))),
    "choose" -> refinement("x" :: nonZero)(x => choose("r" :: BooleanType())(r => r && (x !== int(0)))),
    "call to assume" -> refinement("x" :: nonZero)(x => E(preID)(x)),
    "transitive call to assume" -> refinement("x" :: nonZero)(x => E(pre2ID)(x)),
    "call to choose" -> refinement("x" :: nonZero)(x => E(chooseNonZeroID)(x))
  )

  for ((name, tpe) <- guardedTypes) {
    test(s"path: $name in a quantifier domain") {
      assertValid(instantiates(tpe, int(2)), "in domain")
      assertInvalid(instantiates(tpe, int(0)), "outside base type")
      assertValid(holds(tpe)(_ !== int(0)), "holds")
      assertInvalid(holds(tpe)(_ > int(0)), "doesn't hold")
    }

    test(s"path: $name in a nested quantifier domain") {
      val tpeList = T(listID)(tpe)
      assertValid(instantiates(tpeList, ints(2, 3)), "in domain")
      assertInvalid(instantiates(tpeList, ints(0)), "depth 1 outside base type")
      assertInvalid(instantiates(tpeList, ints(2, 0)), "depth 2 outside base type")
    }

    test(s"path: $name outside of quantifiers") {
      val x = Variable.fresh("x", tpe)
      assertValid(x !== int(0), "free variable")
      assertSat(x === int(2), "free variable")
      val l = Variable.fresh("l", T(listID)(tpe))
      assertValid(((l `is` consID) && (l.getField(tail) `is` consID)) ==> (l.getField(tail).getField(head) !== int(0)), "free list")
      assertSat((l `is` consID) && (l.getField(tail) `is` consID) && (l.getField(tail).getField(head) === int(2)), "free list")
    }
  }

  test("path: Sigma with an assumption in its last component") {
    // (a: {y | y != 0}, {b: BigInt | pre(a) && b > 0})
    val tpe = sigma("a" :: nonZero)(a => refinement("b" :: I)(b => E(preID)(a) && (b > int(0))))
    assertValid(instantiates(tpe, E(int(2), int(1))), "in domain")
    assertInvalid(instantiates(tpe, E(int(0), int(1))), "parameter outside domain")
    assertInvalid(instantiates(tpe, E(int(2), int(0))), "last component outside domain")
    assertValid(holds(tpe)(p => (p._ts1 !== int(0)) && (p._ts2 > int(0))), "holds")
  }

  test("path: assumption in a quantifier body") {
    val tpe = guardedTypes.collectFirst { case ("call to assume", tpe) => tpe }.get
    val g = Variable.fresh("g", I =>: I)
    val hyp = holds(tpe)(w => E(preID)(w) && (g(w) === int(1)))
    assertValid(hyp ==> (g(int(2)) === int(1)), "in domain")
    assertValid(holds(nonZero)(w => E(preID)(w)), "holds")
  }

  /* ==== 3. ADT invariants ==== */

  test("invariant: non-recursive sort, free generator") {
    val p = Variable.fresh("p", Pos)
    assertValid(p.getField(pv) > int(0), "free variable")
    assertInvalid(p.getField(pv) > int(1), "free variable")
    assertValid(holds(Pos)(p => p.getField(pv) > int(0)), "holds")
    assertInvalid(holds(Pos)(p => p.getField(pv) > int(1)), "doesn't hold")
    val o = Variable.fresh("o", T(optionID)(Pos))
    assertValid((o `is` someID) ==> (o.getField(v).getField(pv) > int(0)), "nested in a generic ADT")
    val f = Variable.fresh("f", I =>: Pos)
    assertValid(f(int(1)).getField(pv) > int(0), "free function result")
    assertValid(choose("p" :: Pos)(_ => E(true)).getField(pv) > int(0), "choose result")
  }

  test("invariant: non-recursive sort, contract generator") {
    assertValid(instantiates(Pos, ADT(posConsID, Seq(), Seq(int(1)))), "in domain")
    val p = Variable.fresh("p", Pos)
    assertValid(instantiates(Pos, p), "free variable in domain")
  }

  test("invariant: recursive sort") {
    val l = Variable.fresh("l", PList)
    def at(depth: Int): Expr = (0 until depth).foldLeft(l: Expr)((e, _) => e.getField(pt))
    def consUpTo(depth: Int): Expr = andJoin((0 to depth).map(at(_) `is` pconsID))
    assertValid(consUpTo(0) ==> (at(0).getField(ph) > int(0)), "depth 1")
    assertValid(consUpTo(1) ==> (at(1).getField(ph) > int(0)), "depth 2")
    assertValid(consUpTo(2) ==> (at(2).getField(ph) > int(0)), "depth 3")
    assertInvalid(consUpTo(1) ==> (at(1).getField(ph) > int(1)), "depth 2")
    assertSat(consUpTo(2) && (at(2).getField(ph) === int(5)), "depth 3")
    assertValid(holds(PList)(l => ((l `is` pconsID) && (l.getField(pt) `is` pconsID)) ==>
      (l.getField(pt).getField(ph) > int(0))), "holds at depth 2")
    assertInvalid(holds(PList)(l => ((l `is` pconsID) && (l.getField(pt) `is` pconsID)) ==>
      (l.getField(pt).getField(ph) > int(1))), "doesn't hold at depth 2")
  }

  test("invariant: invariant calls a recursive function") {
    val w = Variable.fresh("w", Wrapper)
    val wList = w.getField(wl)
    assertValid((wList `is` consID) ==> (wList.getField(head) > int(0)), "depth 1")
    assertValid(((wList `is` consID) && (wList.getField(tail) `is` consID)) ==>
      (wList.getField(tail).getField(head) > int(0)), "depth 2")
    assertInvalid(((wList `is` consID) && (wList.getField(tail) `is` consID)) ==>
      (wList.getField(tail).getField(head) > int(1)), "depth 2")
    assertValid(holds(Wrapper)(w => E(allPosID)(w.getField(wl))), "holds")
  }

  /* ==== 4. Type parameters and higher-order values ==== */

  test("hof: type parameters") {
    val aT = TypeParameter.fresh("A")
    val g = Variable.fresh("g", aT =>: I)
    val y = Variable.fresh("y", aT)
    assertUnsat(holds(aT)(_ => E(false)) && (g(y) === int(1)), "inhabited type parameter")
    assertValid(holds(aT)(x => g(x) === int(1)) ==> (g(y) === int(1)), "instantiation")
    // type parameters instantiated with refinements
    val f = Variable.fresh("f", I =>: pos)
    assertValid(E(firstID)(pos)(f) > int(0), "refinement as type argument")
    assertInvalid(E(firstID)(pos)(f) > int(1), "refinement as type argument")
  }

  test("hof: refined function results") {
    val f = Variable.fresh("f", I =>: pos)
    assertValid(f(int(3)) > int(0), "result")
    assertInvalid(f(int(3)) > int(1), "result")
    val h = Variable.fresh("h", I =>: (I =>: pos))
    assertInvalid(h(int(1))(int(2)) > int(1), "curried result")
    val pfun = Variable.fresh("p", PosFun)
    assertValid(pfun.getField(pf)(int(1)) > int(0), "function in an ADT")
    assertInvalid(pfun.getField(pf)(int(1)) > int(1), "function in an ADT")
  }

  test("hof: dependent function results") {
    val incr = pi("a" :: I)(a => refinement("r" :: I)(_ > a))
    val g = Variable.fresh("g", incr)
    assertValid(g(int(5)) > int(5), "result")
    assertUnsat(g(int(5)) === int(5), "result")
  }

  test("hof: refined function arguments") {
    val incr = pi("a" :: pos)(a => refinement("r" :: I)(_ > a))
    val g = Variable.fresh("g", incr)
    assertValid(g(int(1)) > int(1), "argument in domain")
    assertUnsat(g(int(1)) === int(1), "argument in domain")
  }

  test("hof: captures") {
    val b = Variable.fresh("b", FunBox)
    val c = Variable.fresh("c", FunBox)
    val bf = b.getField(fn)
    val cf = c.getField(fn)
    val inc = \("x" :: I)(x => bf(x) + int(1))
    assertSat((bf(int(1)) === int(2)) && (inc(int(1)) === int(3)), "lambda capturing an ADT field")
    assertUnsat((bf(int(1)) === int(2)) && (inc(int(1)) === int(2)), "lambda capturing an ADT field")
    assertSat((cf === inc) && (bf(int(1)) === int(2)), "equal to a lambda capturing another function")
    assertUnsat((cf === inc) && (bf(int(1)) === int(2)) && (cf(int(1)) === int(2)),
      "equal to a lambda capturing another function")
    // A function can't be equal to a lambda that captures it (closures are totally ordered),
    // including when it is captured through an ADT.
    assertUnsat(bf === \("x" :: I)(x => bf(x)), "captured through a field")
    val l = Variable.fresh("l", T(listID)(FunBox))
    val second = l.getField(tail).getField(head).getField(fn)
    val cons2 = (l `is` consID) && (l.getField(tail) `is` consID)
    assertUnsat(cons2 && (second === \("x" :: I)(x => l.getField(tail).getField(head).getField(fn)(x))),
      "captured through a list")
  }

  /* ==== 5. The same type inside and outside of a quantifier domain ==== */

  test("cache: inductive ADT inside and outside of a quantifier domain") {
    val posList = T(listID)(pos)
    val x = Variable.fresh("x", posList)
    val xCons = (x `is` consID) && (x.getField(tail) `is` consID)
    // the free variable's type is unrolled first
    assertValid(xCons ==> instantiates(posList, ints()), "fieldless constructor, free variable first")
    assertInvalid(xCons ==> instantiates(posList, ints(1, 0)), "outside domain, free variable first")
    // the quantifier domain is unrolled first
    assertValid(instantiates(posList, ints()) || !xCons, "fieldless constructor, quantifier first")
    assertInvalid(instantiates(posList, ints(1, 0)) || !xCons, "outside domain, quantifier first")
    // the same value is checked inside and outside of the domain
    assertValid((x `is` nilID) ==> instantiates(posList, x), "free variable in domain")
    assertInvalid(instantiates(posList, ADT(consID, Seq(I), Seq(int(0), x))), "extended free variable")
  }

  test("cache: path-falsifying predicate inside and outside of a quantifier domain") {
    val tpe = guardedTypes.collectFirst { case ("call to assume", tpe) => tpe }.get
    val tpeList = T(listID)(tpe)
    val x = Variable.fresh("x", tpeList)
    val xCons = (x `is` consID) && (x.getField(tail) `is` consID)
    assertValid(xCons ==> instantiates(tpeList, ints(2, 3)), "in domain")
    assertInvalid(xCons ==> instantiates(tpeList, ints(2, 0)), "outside domain")
    assertInvalid(instantiates(tpeList, ADT(consID, Seq(I), Seq(int(0), x))), "extended free variable")
  }

  test("cache: tree inside and outside of a quantifier domain") {
    val t = Variable.fresh("t", Tree)
    val tNode = (t `is` nodeID) && (t.getField(right) `is` nodeID)
    assertValid(tNode ==> instantiates(Tree, node(leaf, 1, leaf)), "in domain")
    assertValid(tNode ==> instantiates(Tree, leaf), "fieldless constructor")
    assertInvalid(tNode ==> instantiates(Tree, node(leaf, 1, node(leaf, 0, leaf))), "outside domain")
    assertInvalid(instantiates(Tree, node(t, 0, leaf)), "extended free variable")
  }


  /* ==== Known issues ====
   *
   * The queries below currently get a wrong or no answer. They are ignored until fixed. */

  ignore("known issue: Pi codomain assumed outside of the domain (samarion/inox#7)") {
    // The codomain of a Pi type is assumed at every application, also for arguments outside
    // of its domain, so these invalid queries are reported valid.
    val incr = pi("a" :: pos)(a => refinement("r" :: I)(_ > a))
    assertInvalid(holds(incr)(h => h(int(0)) > int(0)), "quantifier")
    val g = Variable.fresh("g", incr)
    assertInvalid(g(int(0)) > int(0), "free variable")
  }

  ignore("known issue: models of dependent functions") {
    // The model of `g` must satisfy `r > a` for all `a`, which the extracted lambda doesn't
    // (its default value is constant), so model validation fails and the result is unknown.
    val incr = pi("a" :: I)(a => refinement("r" :: I)(_ > a))
    val g = Variable.fresh("g", incr)
    assertInvalid(g(int(5)) > int(6))
    assertSat(g(int(5)) === int(7))
  }

  ignore("known issue: refined result of a curried function with optFeelingLucky") {
    // With optFeelingLucky, the model of `h` can return a non-positive value, which
    // the model check doesn't catch, so this valid query is reported invalid.
    val h = Variable.fresh("h", I =>: (I =>: pos))
    assertValid(h(int(1))(int(2)) > int(0))
  }

  ignore("known issue: lambda capturing a function from another list") {
    // Without optAssumeChecked, the result is unknown instead of satisfiable.
    val l = Variable.fresh("l", T(listID)(FunBox))
    val l2 = Variable.fresh("l2", T(listID)(FunBox))
    val second = l.getField(tail).getField(head).getField(fn)
    assertSat((l `is` consID) && (l.getField(tail) `is` consID) && (l2 `is` consID) &&
      (second === \("x" :: I)(x => l2.getField(head).getField(fn)(x) + int(1))))
  }

  ignore("known issue: maps in a quantifier domain") {
    // A map value can be decomposed as `rest.updated(k, v)` for any `rest` that agrees with it
    // except at `k`, so the solver can pick a `rest` outside of the domain and falsify the type
    // check of a value that is inside of it. The valid queries are then reported invalid.
    val posMap = MapType(I, pos)
    assertValid(instantiates(posMap, FiniteMap(Seq(), int(1), I, I)), "default only")
    assertValid(instantiates(posMap, FiniteMap(Seq(int(0) -> int(2)), int(1), I, I)), "in domain")
  }

  ignore("known issue: non-empty sets and bags in a quantifier domain") {
    // The type check of a finite set or bag never completes (timeout).
    assertValid(instantiates(SetType(pos), FiniteSet(Seq(int(1)), I)), "set")
    assertValid(instantiates(BagType(pos), FiniteBag(Seq(int(1) -> int(1)), I)), "bag")
    val x = Variable.fresh("x", I)
    val b = Variable.fresh("b", BagType(pos))
    assertValid((b === FiniteBag(Seq(x -> int(1)), I)) ==> (x > int(0)), "free bag variable")
  }

  ignore("known issue: elements of unbounded collections") {
    // Sets, maps and bags can be infinite, so their type checks never complete.
    val x = Variable.fresh("x", I)
    assertValid(holds(SetType(pos))(s => Forall(Seq(x.toVal), ElementOfSet(x, s) ==> (x > int(0)))), "set")
    assertValid(holds(MapType(I, pos))(m => Forall(Seq(x.toVal), MapApply(m, x) > int(0))), "map")
    assertValid(holds(BagType(pos))(b => Forall(Seq(x.toVal), (MultiplicityInBag(x, b) > int(0)) ==> (x > int(0)))), "bag")
    val m = Variable.fresh("m", MapType(I, pos))
    assertValid(MapApply(m, x) > int(0), "free map variable")
  }

  ignore("known issue: quantifier instantiated with a free variable of an inductive type") {
    // The domain check of `x` (contract generator) doesn't use the type of `x` (free generator),
    // and needs to unfold `x` entirely, so the instantiation is never enabled (timeout).
    val posList = T(listID)(pos)
    val x = Variable.fresh("x", posList)
    assertValid(instantiates(posList, x))
  }

  ignore("known issue: assumption in a quantifier body") {
    // `pre(0)` is unrolled for the instantiation with 0, outside of the domain, and the
    // result is unknown instead of invalid.
    val tpe = guardedTypes.collectFirst { case ("call to assume", tpe) => tpe }.get
    val g = Variable.fresh("g", I =>: I)
    assertInvalid(holds(tpe)(w => E(preID)(w) && (g(w) === int(1))) ==> (g(int(0)) === int(1)), "refined domain")
    assertInvalid(holds(nonZero)(w => E(preID)(w) && (g(w) === int(1))) ==> (g(int(0)) === int(1)), "base domain")
  }

  ignore("known issue: empty type parameter (samarion/inox#30)") {
    // Type parameters are currently assumed to be inhabited, so this is unsatisfiable.
    assertSat(holds(TypeParameter.fresh("A"))(_ => E(false)))
  }

  ignore("known issue: empty refinement in a quantifier domain") {
    // A quantifier over an empty type holds vacuously, but the result is unknown.
    assertSat(holds(refinement("z" :: I)(_ => E(false)))(_ => E(false)))
  }
}
