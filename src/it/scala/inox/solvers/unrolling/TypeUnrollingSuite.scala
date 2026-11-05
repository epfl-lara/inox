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

  // case class DepBox(db: (a: {y | y > 0}) => {r: BigInt | r > a})
  val depBoxID = FreshIdentifier("DepBox")
  val depBoxConsID = FreshIdentifier("DepBox")
  val db = FreshIdentifier("db")
  val depBoxSort = mkSort(depBoxID)() { _ => Seq((depBoxConsID, Seq(ValDef(db, pi("a" :: pos)(a => refinement("r" :: I)(_ > a)))))) }
  val DepBox = T(depBoxID)()

  // def first[A](f: BigInt => A): A = f(0)
  val firstID = FreshIdentifier("first")
  val first = mkFunDef(firstID)("A") { case Seq(aT) => (
    Seq("f" :: (I =>: aT)), aT, { case Seq(f) => f(int(0)) })
  }

  // def mkIncr(): (a: {y | y > 0}) => {r: BigInt | r > a} = (x: BigInt) => if (x > 0) x + 1 else 0
  val mkIncrID = FreshIdentifier("mkIncr")
  val mkIncr = mkFunDef(mkIncrID)() { _ => (
    Seq(), pi("a" :: pos)(a => refinement("r" :: I)(_ > a)), { _ =>
      \("x" :: I)(x => if_ (x > int(0)) { x + int(1) } else_ { int(0) })
    })
  }

  val symbols = baseSymbols
    .withFunctions(Seq(pre, pre2, chooseNonZero, isPositive, posInv, plistInv, allPos, wrapperInv, first, mkIncr))
    .withSorts(Seq(boxSort, treeSort, posSort, plistSort, wrapperSort, funBoxSort, posFunSort, depBoxSort))
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
  private def solverFor(e: Expr, checkModels: Boolean = true)(using ctx: Context) =
    SimpleSolverAPI(program.getSolver(ctx.withOpts(optCheckModels(checkModels && !containsQuantifiers(e)))))

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

  // For models of functions with function-typed domains, whose validation quantifies over functions
  def assertSatUnchecked(e: Expr, clue: String = "")(using Context): Unit = {
    val res = solverFor(e, checkModels = false).solveSAT(e)
    assert(res.isSAT, s"$clue: expected ${show(e)} to be satisfiable, but got $res")
  }

  // For queries that are unsatisfiable but the solver can't refute, it mustn't report a model either
  def assertNotSat(e: Expr, clue: String = "")(using Context): Unit = {
    val res = solverFor(e).solveSAT(e)
    assert(!res.isSAT, s"$clue: expected ${show(e)} not to be satisfiable, but got $res")
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

  /* ---- Pi codomains only hold inside of the domain ---- */

  // (a: {y | y > 0}) => {r: BigInt | r > a}
  val posIncr = pi("a" :: pos)(a => refinement("r" :: I)(_ > a))

  test("Pi codomain inside and outside of the domain") {
    val g = Variable.fresh("g", posIncr)
    val x = Variable.fresh("x", I)
    assertValid(g(int(1)) > int(1), "inside")
    assertInvalid(g(int(0)) > int(0), "outside")
    assertValid((x > int(5)) ==> (g(x) > int(5)), "symbolic argument inside")
    assertInvalid((x < int(5)) ==> (g(x) > int(0)), "symbolic argument outside")
    assertInvalid(holds(posIncr)(h => h(int(0)) > int(0)), "quantifier")
    val f = Variable.fresh("f", I =>: I)
    assertInvalid((f === g) ==> (f(int(0)) > int(0)), "through an equal function")
    assertValid((f === g) ==> (f(int(1)) > int(1)), "inside through an equal function")
  }

  test("Pi codomain with a dependent domain") {
    // (a: BigInt, b: {y | y > a}) => {r: BigInt | r > 0}
    val dep = {
      val a = "a" :: I
      PiType(Seq(a, "b" :: refinement("y" :: I)(_ > a.toVariable)), pos)
    }
    val g = Variable.fresh("g", dep)
    assertValid(g(int(1), int(2)) > int(0), "inside")
    assertInvalid(g(int(2), int(1)) > int(0), "outside")
  }

  test("Pi codomain of a function result") {
    // The result type of `mkIncr` is assumed, which must not constrain its result outside of
    // the domain, where it returns 0.
    val incr = E(mkIncrID)()
    assertValid(incr(int(1)) > int(1), "inside")
    assertValid(incr(int(0)) === int(0), "outside")
    assertInvalid(incr(int(0)) > int(5), "outside, not contradictory")
  }

  test("Pi domain of a quantifier is instantiated by its members") {
    assertValid(instantiates(posIncr, \("x" :: I)(x => x + int(1))), "in domain")
    assertInvalid(instantiates(posIncr, \("x" :: I)(x => x - int(1))), "outside domain")
    assertValid(instantiates(posIncr, \("x" :: I)(x => if_ (x > int(0)) { x + int(1) } else_ { int(0) })),
      "outside codomain outside of the domain")
    assertInvalid(instantiates(posIncr, Variable.fresh("f", I =>: I)), "free function")
  }

  test("Pi domain that depends on an outer variable") {
    val n = Variable.fresh("n", I)
    val m = Variable.fresh("m", I)
    // (a: {y | y > n}) => {r: BigInt | r > a}
    def above(n: Expr) = pi("a" :: refinement("y" :: I)(_ > n))(a => refinement("r" :: I)(_ > a))
    val g = Variable.fresh("g", above(n))
    val h = Variable.fresh("h", above(m))
    assertValid(g(n + int(1)) > n + int(1), "inside")
    assertInvalid(g(n) > n, "outside")
    assertInvalid((m > n) ==> (h(n + int(1)) > n + int(1)), "same argument, other domain")
    assertValid((g(n + int(1)) > n + int(1)) && ((m < n) ==> (h(n + int(1)) > n + int(1))), "both domains")

    // F: (k: (x: BigInt) => {r | r > n}) => {r | r > 0}, whose domain captures `n`
    val F = Variable.fresh("F", PiType(Seq("k" :: pi("x" :: I)(_ => refinement("r" :: I)(_ > n))), pos))
    assertValid(F(\("x" :: I)(_ => n + int(1))) > int(0), "captured, inside")
    assertSatUnchecked(F(\("x" :: I)(_ => n)) <= int(0), "captured, outside")
  }

  // Function-typed domains are checked at fresh arguments, without quantifiers
  test("Pi codomain with function-typed domains") {
    val refinedFun = refinement("h" :: (I =>: I))(h => h(int(0)) > int(0))
    val piFun = pi("x" :: I)(_ => pos)
    val const = (i: Int) => \("x" :: I)(_ => int(i))
    val f = Variable.fresh("f", I =>: I)

    val F = Variable.fresh("F", PiType(Seq("g" :: refinedFun), pos))
    assertValid(F(const(1)) > int(0), "refined, inside")
    assertInvalid(F(const(-1)) > int(0), "refined, outside")
    assertValid((f(int(0)) > int(0)) ==> (F(f) > int(0)), "refined, free function inside")
    assertInvalid((f(int(0)) <= int(0)) ==> (F(f) > int(0)), "refined, free function outside")

    val G = Variable.fresh("G", PiType(Seq("g" :: piFun), pos))
    val p = Variable.fresh("p", piFun)
    assertValid(G(const(1)) > int(0), "Pi, inside")
    assertValid(G(p) > int(0), "Pi, free function inside")
    assertSatUnchecked(G(const(-1)) <= int(0), "Pi, outside")
    assertSatUnchecked(G(f) <= int(0), "Pi, free function outside")
    assertSatUnchecked(G(p) > int(5), "Pi, counterexample inside")

    // H: ((k: (BigInt => {r | r > 0})) => {r | r > 0}) => {r | r > 0}
    val k = "k" :: piFun
    val H = Variable.fresh("H", PiType(Seq("h" :: PiType(Seq(k), pos)), pos))
    assertValid(H(\(k)(k => k(int(0)))) > int(0), "higher-order, inside")
    assertSatUnchecked(H(\(k)(k => k(int(0)) - int(1))) <= int(0), "higher-order, outside")

    // Every function lies in (x: {y | false}) => {r | r > 0}
    val Em = Variable.fresh("E", PiType(Seq("g" :: pi("x" :: refinement("y" :: I)(_ => E(false)))(_ => pos)), pos))
    assertValid(Em(f) > int(0), "empty domain")
    assertSatUnchecked(Em(f) > int(5), "empty domain, counterexample")

    // List[BigInt => {r | r > 0}]
    val L = Variable.fresh("L", PiType(Seq("l" :: T(listID)(I =>: pos)), pos))
    def funs(fs: Expr*): Expr = list(I =>: pos)(fs*)
    assertValid(L(funs()) > int(0), "ADT, fieldless constructor")
    assertValid(L(funs(const(1), const(2))) > int(0), "ADT, inside")
    assertSatUnchecked(L(funs(const(1), const(-1))) <= int(0), "ADT, outside")
  }

  test("models of dependent functions") {
    // The models of these functions must lie in their types, including at arguments the
    // query doesn't apply them to.
    val g = Variable.fresh("g", posIncr)
    val x = Variable.fresh("x", I)
    assertSat(g(int(0)) <= int(0), "outside of the domain")
    assertSat((x > int(5)) && (g(x) > int(7)) && (g(int(-1)) < int(0)), "inside and outside")

    val incr = pi("a" :: I)(a => refinement("r" :: I)(_ > a))
    val h = Variable.fresh("h", incr)
    assertInvalid(h(int(5)) > int(6), "dependent codomain")
    assertSat(h(int(5)) === int(7), "dependent codomain")

    // (a: {y | y > 0}) => (b: BigInt) => {r: BigInt | a > 0 && r > b}, whose codomain is
    // empty outside of the domain
    val curried = Variable.fresh("c", pi("a" :: pos)(a => pi("b" :: I)(b => refinement("r" :: I)(r => (a > int(0)) && (r > b)))))
    assertSat(curried(int(1))(int(2)) > int(10), "curried, inside")
    assertSat(curried(int(0))(int(2)) < int(0), "curried, outside")

    // (a: {y | y > 0}) => ({r: BigInt | r > a}, {s: BigInt | s < a})
    val pair = Variable.fresh("p", pi("a" :: pos)(a => T(refinement("r" :: I)(_ > a), refinement("s" :: I)(_ < a))))
    assertSat(pair(int(1))._ts1 > int(5), "tuple, inside")
    assertSat(pair(int(0))._ts1 < int(0), "tuple, outside")

    // (a: {y | y > 0}) => (b: {y | y > a}, {c: BigInt | c > b})
    val dep = Variable.fresh("d", pi("a" :: pos)(a => sigma("b" :: refinement("y" :: I)(_ > a))(b => refinement("c" :: I)(_ > b))))
    assertSat(dep(int(1))._ts1 === int(3), "Sigma, inside")
    assertSat(dep(int(0))._ts2 < int(0), "Sigma, outside")
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

  test("hof: captures") { ctx ?=>
    // compares functions, which needs the intensional semantics of function equality
    given Context = ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))
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


  /* ==== 6. Dependent types in other positions ==== */

  test("Sigma with an unused refined parameter") {
    // (a: {y | y > 0}, BigInt)
    val t = sigma("a" :: pos)(_ => I)
    assertValid(instantiates(t, E(int(1), int(0))), "in domain")
    assertInvalid(instantiates(t, E(int(0), int(0))), "outside domain")
    assertValid(holds(t)(p => p._ts1 > int(0)), "holds")
    val v = Variable.fresh("v", t)
    assertValid(v._ts1 > int(0), "free variable")
  }

  test("Sigma containing a Pi") {
    // (a: {y | y > 0}, (x: {y | y > a}) => {r: BigInt | r > x})
    val t = sigma("a" :: pos)(a => pi("x" :: refinement("y" :: I)(_ > a))(x => refinement("r" :: I)(_ > x)))
    assertValid(holds(t)(p => p._ts2(p._ts1 + int(1)) > p._ts1 + int(1)), "holds inside")
    assertInvalid(holds(t)(p => p._ts2(p._ts1) > p._ts1), "outside")
    val v = Variable.fresh("v", t)
    assertValid(v._ts2(v._ts1 + int(1)) > v._ts1 + int(1), "free variable inside")
    assertInvalid(v._ts2(v._ts1) > v._ts1, "free variable outside")
  }

  test("Pi in an ADT field") {
    val b = Variable.fresh("b", DepBox)
    assertValid(b.getField(db)(int(1)) > int(1), "inside")
    assertInvalid(b.getField(db)(int(0)) > int(0), "outside")
    assertValid(holds(DepBox)(b => b.getField(db)(int(2)) > int(2)), "quantifier, inside")
    assertInvalid(holds(DepBox)(b => b.getField(db)(int(0)) > int(0)), "quantifier, outside")
    val bad = ADT(depBoxConsID, Seq(), Seq(\("x" :: I)(x => x)))
    assertInvalid(instantiates(DepBox, bad), "constructed outside of the type")
    assertValid(instantiates(DepBox, ADT(depBoxConsID, Seq(), Seq(\("x" :: I)(x => x + int(1))))), "constructed")
  }

  test("Pi in tuples and maps") {
    val t = Variable.fresh("t", T(posIncr, I))
    assertValid(t._ts1(int(1)) > int(1), "tuple, inside")
    assertInvalid(t._ts1(int(0)) > int(0), "tuple, outside")
    val m = Variable.fresh("m", MapType(I, posIncr))
    // Proving properties of map values is a known issue (see "elements of unbounded collections")
    assertSat(MapApply(m, int(3))(int(1)) === int(5), "map, inside")
    val incr = \("x" :: I)(x => if_ (x > int(0)) { x + int(1) } else_ { int(0) })
    assertSat((m === FiniteMap(Seq(), incr, I, posIncr)) && (MapApply(m, int(3))(int(0)) === int(0)), "map, literal")
    assertInvalid(MapApply(m, int(3))(int(0)) > int(0), "map, outside")
  }

  test("choose of a Pi") {
    val c = choose("f" :: posIncr)(_ => E(true))
    assertValid(c(int(1)) > int(1), "inside")
    assertInvalid(c(int(0)) > int(0), "outside")
    val d = choose("f" :: posIncr)(f => f(int(1)) === int(5))
    assertValid(d(int(1)) === int(5), "constrained")
    assertInvalid(d(int(0)) > int(0), "constrained, outside")
    val p = choose("f" :: (I =>: I))(f => f(int(1)) === int(5))
    assertValid(p(int(1)) === int(5), "plain function type")
  }

  test("curried Pi with a dependent inner domain") {
    // (a: {y | y > 0}) => (b: {y | y > a}) => {r: BigInt | r > b}
    val t = pi("a" :: pos)(a => pi("b" :: refinement("y" :: I)(_ > a))(b => refinement("r" :: I)(_ > b)))
    val c = Variable.fresh("c", t)
    assertValid(c(int(1))(int(2)) > int(2), "inside")
    assertInvalid(c(int(1))(int(1)) > int(1), "inner argument outside")
    assertInvalid(c(int(0))(int(5)) > int(5), "outer argument outside")
    assertValid(holds(t)(w => w(int(1))(int(2)) > int(2)), "quantifier, inside")
    assertInvalid(holds(t)(w => w(int(1))(int(1)) > int(1)), "quantifier, outside")
    assertSat(c(int(1))(int(1)) < int(0), "model")
  }

  test("lambdas with refined parameters as Pi arguments") {
    // H: (h: (a: {y | y > 0}) => {r | r > a}) => {r | r > 0}
    val H = Variable.fresh("H", PiType(Seq("h" :: posIncr), pos))
    assertValid(H(\("x" :: pos)(x => x + int(1))) > int(0), "inside")
    assertValid(H(\("x" :: I)(x => if_ (x > int(0)) { x + int(1) } else_ { int(-5) })) > int(0),
      "inside, arbitrary outside of the domain")
    val n = Variable.fresh("n", I)
    assertValid((n >= int(1)) ==> (H(\("x" :: I)(x => x + n)) > int(0)), "capturing, inside")
    assertSatUnchecked((n === int(0)) && (H(\("x" :: I)(x => x + n)) <= int(0)), "capturing, outside")
  }

  test("equality between functions with different domains") {
    val f = Variable.fresh("f", posIncr)
    // (a: BigInt) => {r: BigInt | r > a}
    val g = Variable.fresh("g", pi("a" :: I)(a => refinement("r" :: I)(_ > a)))
    assertValid((f === g) ==> (f(int(0)) > int(0)), "codomain of the wider domain")
    assertInvalid((f === g) ==> (f(int(0)) > int(1)), "nothing more")
    assertSat((f === g) && (f(int(1)) === int(2)), "model")
  }

  test("negative quantifier over a function type") {
    assertValid(holds(I =>: pos)(w => w(int(0)) > int(0)), "holds")
    assertInvalid(holds(I =>: pos)(w => w(int(0)) > int(1)), "doesn't hold")
    assertInvalid(holds(posIncr)(w => w(int(1)) > int(2)), "Pi, doesn't hold")
    assertValid(holds(posIncr)(w => w(w(int(1))) > int(2)), "Pi, nested applications")
  }

  test("models of Pi-typed functions with ADT codomains") {
    // (a: {y | y > 0}) => List[{r: BigInt | r > a}]
    val g = Variable.fresh("g", pi("a" :: pos)(a => T(listID)(refinement("r" :: I)(_ > a))))
    assertSat(g(int(1)) === list(I)(int(5)), "inside")
    assertSat((g(int(1)) `is` consID) && (g(int(2)) `is` nilID), "two applications")
    assertInvalid((g(int(1)) `is` consID) ==> (g(int(1)).getField(head) > int(2)), "invalid")
  }

  test("models of dependent values in other positions") {
    val t = sigma("a" :: pos)(a => pi("x" :: refinement("y" :: I)(_ > a))(x => refinement("r" :: I)(_ > x)))
    val v = Variable.fresh("v", t)
    assertSat(v._ts2(v._ts1 + int(1)) === v._ts1 + int(5), "Sigma")
    val b = Variable.fresh("b", DepBox)
    assertSat((b.getField(db)(int(1)) === int(7)) && (b.getField(db)(int(2)) === int(3)), "ADT field")
    val d = choose("f" :: posIncr)(f => f(int(1)) === int(5))
    assertSat(d(int(2)) === int(10), "choose")
    val l = Variable.fresh("l", T(listID)(posIncr))
    assertSat((l `is` consID) && (l.getField(head)(int(1)) === int(4)), "list")
  }

  test("Pi with a predicate function in its domain") {
    // (a: {y | isPositive(y)}) => {r: BigInt | r > a}
    val t = pi("a" :: refinement("y" :: I)(y => E(isPositiveID)(y)))(a => refinement("r" :: I)(_ > a))
    val f = Variable.fresh("f", t)
    assertValid(f(int(1)) > int(1), "inside")
    assertInvalid(f(int(0)) > int(0), "outside")
    assertValid(holds(t)(w => w(int(2)) > int(2)), "quantifier, inside")
    assertInvalid(holds(t)(w => w(int(0)) > int(0)), "quantifier, outside")
    assertSat(f(int(0)) === int(-3), "model")
  }

  test("Pi in an inductive ADT") {
    val l = Variable.fresh("l", T(listID)(posIncr))
    assertValid((l `is` consID) ==> (l.getField(head)(int(1)) > int(1)), "inside")
    assertInvalid((l `is` consID) ==> (l.getField(head)(int(0)) > int(0)), "outside")
    assertValid(((l `is` consID) && (l.getField(tail) `is` consID)) ==>
      (l.getField(tail).getField(head)(int(3)) > int(3)), "tail")
  }

  test("Pi as a type argument") {
    val g = Variable.fresh("g", I =>: posIncr)
    assertValid(E(firstID)(posIncr)(g)(int(1)) > int(1), "inside")
    assertInvalid(E(firstID)(posIncr)(g)(int(0)) > int(0), "outside")
  }

  test("Pi applied to arguments that may lie outside of the domain") {
    val f = Variable.fresh("f", posIncr)
    val x = Variable.fresh("x", I)
    assertValid((x > int(0)) ==> (f(x) > x), "guarded")
    assertInvalid(f(x) > x, "unguarded")
    assertValid(f(if_ (x > int(0)) { x } else_ { int(1) }) > int(0), "conditional argument")
  }

  test("Pi with a tuple domain") {
    // (p: {q: (BigInt, BigInt) | q._1 < q._2}) => {r: BigInt | p._1 < r && r < p._2}
    val t = pi("p" :: refinement("q" :: T(I, I))(q => q._ts1 < q._ts2))(p => refinement("r" :: I)(r => (p._ts1 < r) && (r < p._ts2)))
    val f = Variable.fresh("f", t)
    assertValid(f(E(int(1), int(3))) === int(2), "inside")
    assertInvalid(f(E(int(3), int(1))) === int(2), "outside")
    assertSat(f(E(int(0), int(5))) === int(3), "model")
    assertUnsat(f(E(int(0), int(1))) === int(0), "empty codomain")
  }

  test("Pi equal to a lambda outside of it") {
    // The type of a free function is only assumed at its applications, so its equality to a lambda
    // outside of the type isn't refuted. The model is rejected instead (see the known issue below).
    val f = Variable.fresh("f", posIncr)
    assertNotSat(f === \("x" :: I)(x => x), "identity")
    assertUnsat((f === \("x" :: I)(x => x)) && (f(int(1)) === int(1)), "applied")
    val g = Variable.fresh("g", I =>: pos)
    assertNotSat(g === \("x" :: I)(x => x), "refined codomain")
    assertSat(f === \("x" :: I)(x => if_ (x > int(0)) { x + int(1) } else_ { int(-1) }), "inside")
  }

  /* ==== Known issues ====
   *
   * The queries below currently get a wrong or no answer. They are ignored until fixed. */

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

  ignore("known issue: free function equal to a lambda outside of its type") {
    val f = Variable.fresh("f", posIncr)
    assertUnsat(f === \("x" :: I)(x => x), "identity")
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
