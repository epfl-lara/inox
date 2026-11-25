/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** A sort with a custom equality (`HasADTEquality`), nested in sorts that don't have one.
  *
  * `A(n, tag)` values are equal when their `n` are, whatever their `tag`. Its equality must decide
  * the equality of the values that hold it: in fields, tuples and lists, and in sorts that recurse
  * through another sort (`Tree` through `List[Tree]`, `T1` and `T2` through each other), whichever
  * of these types the solver meets first. The evaluator, and the solvers that decide ground
  * formulas with it, must agree.
  */
class NestedCustomEqualitySuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses._

  val aID = FreshIdentifier("A")
  val aCons = FreshIdentifier("A")
  val nID = FreshIdentifier("n")
  val tagID = FreshIdentifier("tag")
  val eqAID = FreshIdentifier("eqA")
  val aSort = mkSort(aID, HasADTEquality(eqAID))() { _ =>
    Seq((aCons, Seq(ValDef(nID, IntegerType()), ValDef(tagID, IntegerType()))))
  }
  val eqAFd = mkFunDef(eqAID)() { _ => (
    Seq("x" :: T(aID)(), "y" :: T(aID)()), BooleanType(), {
      case Seq(x, y) => Equals(x.getField(nID), y.getField(nID))
    })
  }

  val wrapID = FreshIdentifier("Wrap")
  val wrapCons = FreshIdentifier("Wrap")
  val wrapSort = mkSort(wrapID)() { _ => Seq((wrapCons, Seq(ValDef(FreshIdentifier("a"), T(aID)())))) }

  val listID = FreshIdentifier("List")
  val consID = FreshIdentifier("Cons")
  val nilID = FreshIdentifier("Nil")
  val listSort = mkSort(listID)("X") { case Seq(x) => Seq(
    (nilID, Seq()),
    (consID, Seq(ValDef(FreshIdentifier("head"), x), ValDef(FreshIdentifier("tail"), T(listID)(x)))))
  }

  // Tree = Node(kids: List[Tree]) | Leaf(a: A), whose `Node` comes first
  val treeID = FreshIdentifier("Tree")
  val nodeID = FreshIdentifier("Node")
  val leafID = FreshIdentifier("Leaf")
  val treeSort = mkSort(treeID)() { _ => Seq(
    (nodeID, Seq(ValDef(FreshIdentifier("kids"), T(listID)(T(treeID)())))),
    (leafID, Seq(ValDef(FreshIdentifier("a"), T(aID)()))))
  }

  // T1 = C1(T2) | D1(A) and T2 = C2(T1) | D2: only T1 holds an `A` directly
  val t1ID = FreshIdentifier("T1")
  val c1ID = FreshIdentifier("C1")
  val d1ID = FreshIdentifier("D1")
  val t2ID = FreshIdentifier("T2")
  val c2ID = FreshIdentifier("C2")
  val d2ID = FreshIdentifier("D2")
  val t1Sort = mkSort(t1ID)() { _ => Seq(
    (c1ID, Seq(ValDef(FreshIdentifier("t2"), T(t2ID)()))),
    (d1ID, Seq(ValDef(FreshIdentifier("a"), T(aID)()))))
  }
  val t2Sort = mkSort(t2ID)() { _ => Seq(
    (c2ID, Seq(ValDef(FreshIdentifier("t1"), T(t1ID)()))),
    (d2ID, Seq()))
  }

  override protected def symbols: Symbols =
    NoSymbols.withSorts(Seq(aSort, wrapSort, listSort, treeSort, t1Sort, t2Sort)).withFunctions(Seq(eqAFd))
  given Symbols = symbols

  val AT = T(aID)()
  def A(n: Int, tag: Int): Expr = ADT(aCons, Seq(), Seq(E(BigInt(n)), E(BigInt(tag))))
  def wrap(a: Expr): Expr = ADT(wrapCons, Seq(), Seq(a))
  def list(es: Expr*)(tpe: Type): Expr =
    es.foldRight(ADT(nilID, Seq(tpe), Seq()): Expr)((h, t) => ADT(consID, Seq(tpe), Seq(h, t)))
  def leaf(a: Expr): Expr = ADT(leafID, Seq(), Seq(a))
  def node(kids: Expr*): Expr = ADT(nodeID, Seq(), Seq(list(kids*)(T(treeID)())))
  def c1(e: Expr): Expr = ADT(c1ID, Seq(), Seq(e))
  def d1(e: Expr): Expr = ADT(d1ID, Seq(), Seq(e))
  def c2(e: Expr): Expr = ADT(c2ID, Seq(), Seq(e))
  def pair(e: Expr): Expr = Tuple(Seq(e, E(BigInt(1))))

  val a = Variable.fresh("a", AT)
  val b = Variable.fresh("b", AT)
  /** `a` and `b` are equal, but not structurally. */
  val equalNotSame = And(Equals(a.getField(nID), b.getField(nID)), Not(Equals(a.getField(tagID), b.getField(tagID))))
  val x = A(1, 0)
  val y = A(1, 5)
  val z = A(2, 0)

  /** The ways to hold an `A` in a value whose sort has no custom equality. */
  val holders: Seq[(String, Expr => Expr)] = Seq(
    "a field" -> wrap,
    "a tuple" -> pair,
    "a list" -> (e => list(e)(AT)),
    "a list of fields" -> (e => list(wrap(e))(T(wrapID)())),
    "a sort that recurses through a list" -> (e => node(leaf(e))),
    "a list of such a sort" -> (e => list(node(leaf(e)))(T(treeID)())),
    "mutually recursive sorts, from the one without an A" -> (e => c2(c1(c2(d1(e))))),
    "mutually recursive sorts, from the one with an A" -> (e => c1(c2(d1(e)))),
  )

  def valid(ctx: Context, e: Expr): Unit = solver(ctx).solveSAT(Not(e)) match {
    case Unsat => // OK
    case SatWithModel(model) => fail(s"Found a counterexample to valid formula ${e.asString}: ${model.vars}")
    case res => fail(s"Couldn't prove ${e.asString}, got $res")
  }

  def evaluatesTo(ctx: Context, e: Expr, expected: Boolean): Unit =
    program.getEvaluator(ctx).eval(e).result match {
      case Some(BooleanLiteral(`expected`)) => // OK
      case res => fail(s"${e.asString} should evaluate to $expected, got $res")
    }

  for ((name, hold) <- holders) {
    test(s"Custom equality within $name", ADTs, Integers) { ctx =>
      valid(ctx, Implies(equalNotSame, Equals(hold(a), hold(b))))
      valid(ctx, Implies(Not(Equals(a.getField(nID), b.getField(nID))), Not(Equals(hold(a), hold(b)))))
    }

    test(s"Ground custom equality within $name") { ctx =>
      valid(ctx, Equals(hold(x), hold(y)))
      valid(ctx, Not(Equals(hold(x), hold(z))))
    }

    test(s"Evaluation of custom equality within $name") { ctx =>
      evaluatesTo(ctx, Equals(hold(x), hold(y)), true)
      evaluatesTo(ctx, Equals(hold(x), hold(z)), false)
    }
  }

  test("Custom equality within sorts met in either order", ADTs, Integers) { ctx =>
    // the sort that recurses through the other one, and the other one, in the same query
    valid(ctx, Implies(equalNotSame, And(Equals(node(leaf(a)), node(leaf(b))), Equals(list(leaf(a))(T(treeID)()), list(leaf(b))(T(treeID)())))))
    valid(ctx, Implies(equalNotSame, And(Equals(c2(d1(a)), c2(d1(b))), Equals(c1(c2(d1(a))), c1(c2(d1(b)))))))
  }

  test("Evaluation of custom equality within sets and maps") { ctx =>
    evaluatesTo(ctx, ElementOfSet(wrap(y), FiniteSet(Seq(wrap(x)), T(wrapID)())), true)
    evaluatesTo(ctx, ElementOfSet(wrap(z), FiniteSet(Seq(wrap(x)), T(wrapID)())), false)
    evaluatesTo(ctx, Equals(FiniteSet(Seq(wrap(x), wrap(y)), T(wrapID)()), FiniteSet(Seq(wrap(y)), T(wrapID)())), true)
    val m = FiniteMap(Seq(wrap(x) -> E(BigInt(1))), E(BigInt(0)), T(wrapID)(), IntegerType())
    evaluatesTo(ctx, Equals(MapApply(m, wrap(y)), E(BigInt(1))), true)
    val byValue = FiniteMap(Seq(E(BigInt(1)) -> x), z, IntegerType(), AT)
    evaluatesTo(ctx, Equals(byValue, FiniteMap(Seq(E(BigInt(1)) -> y), z, IntegerType(), AT)), true)
    evaluatesTo(ctx, Equals(byValue, FiniteMap(Seq(), z, IntegerType(), AT)), false)
  }
}
