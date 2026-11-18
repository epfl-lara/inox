/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** The partial operations (see [[ast.SymbolOps.definedness]]) where they fail, on every solver.
  *
  * By default, a partial operation that fails makes its path infeasible, like an error. Under
  * `optAssumeChecked`, the front-end has checked that it doesn't fail, and it is total with an
  * unspecified value where it would fail, as in SMT-LIB. The template generator only guards the
  * partial operations in the default mode, so under `optAssumeChecked` each solver's own encoding
  * decides what happens where they fail, and the solvers must agree on it: the value is
  * unspecified, but it is a function of the operation's arguments.
  *
  * Later features, such as functions whose equality depends on where they fail, take paths that
  * fail in the default mode too, so a solver that gives a failing operation no value at all (and
  * makes every path through it infeasible) answers wrongly there as well.
  */
class PartialOperationSemanticsSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  private val listID = FreshIdentifier("List")
  private val nilID = FreshIdentifier("Nil")
  private val consID = FreshIdentifier("Cons")
  private val headID = FreshIdentifier("head")
  private val tailID = FreshIdentifier("tail")

  private val listSort = mkSort(listID)() { _ => Seq(
    (nilID, Seq()),
    (consID, Seq(ValDef(headID, IntegerType()), ValDef(tailID, T(listID)())))
  )}

  override protected def symbols: Symbols = NoSymbols.withSorts(Seq(listSort))

  given Symbols = symbols

  /** A partial operation, applied to fresh variables of `argTypes`, which fails on the arguments
    * that satisfy `fails`.
    *
    * @param differs Whether the operation may take different values on different arguments
    *                where it fails, as `x / 0` does for different `x`.
    */
  private case class PartialOperation(
    argTypes: Seq[Type],
    op: Seq[Expr] => Expr,
    fails: Seq[Expr] => Expr,
    differs: Boolean
  )

  private val int = IntegerType()
  private val real = RealType()
  private def intZero(args: Seq[Expr]): Expr = Equals(args(1), IntegerLiteral(0))
  private def realZero(args: Seq[Expr]): Expr = Equals(args(1), FractionLiteral(0, 1))

  private def binary(op: (Expr, Expr) => Expr): Seq[Expr] => Expr = { case Seq(l, r) => op(l, r) }

  /** Checks that `po` fails where it should: by default, the paths that reach a failing
    * operation are infeasible, and under assume-checked, the operation has an unspecified
    * value that only depends on its arguments. */
  private def checkPartial(ctx: Context, po: PartialOperation): Unit = {
    def fresh() = po.argTypes.zipWithIndex.map { case (tpe, i) => Variable.fresh(s"x$i", tpe) }
    val args = fresh()
    val result = po.op(args)
    val value = Variable.fresh("v", result.getType)

    def valid(s: SimpleSolverAPI { val program: InoxProgram }, e: Expr): Option[Boolean] = s.solveVALID(e)

    // By default, every path that reaches the failing operation is infeasible, whatever value
    // is expected from it
    // (also when models are extracted early, as with feeling-lucky, before the solver has seen
    // the invariants of the encoded theories)
    for (s <- Seq(solver(ctx), solver(ctx.withOpts(unrolling.optFeelingLucky(true))))) {
      assert(valid(s, Implies(po.fails(args), Equals(result, value))) contains true,
        s"by default, the paths where '$result' fails should be infeasible")
      assert(valid(s, Implies(po.fails(args), Not(Equals(result, value)))) contains true,
        s"by default, the paths where '$result' fails should be infeasible")
    }

    // Under assume-checked, the failing operation has an unspecified value...
    val cs = solver(ctx.withOpts(optAssumeChecked(true)))
    assert(valid(cs, Implies(po.fails(args), Equals(result, value))) contains false,
      s"under assume-checked, '$result' should have some value where it fails")
    assert(valid(cs, Implies(po.fails(args), Not(Equals(result, value)))) contains false,
      s"under assume-checked, '$result' should have any value where it fails")

    // ... which only depends on the operation's arguments
    val others = fresh()
    val sameArgs = andJoin((args zip others).map { case (a, o) => Equals(a, o) })
    assert(valid(cs, Implies(And(po.fails(args), sameArgs), Equals(result, po.op(others)))) contains true,
      s"under assume-checked, '$result' should be a function of its arguments where it fails")
    if (po.differs) {
      assert(valid(cs, Implies(And(po.fails(args), po.fails(others)), Equals(result, po.op(others)))) contains false,
        s"under assume-checked, '$result' should depend on its arguments where it fails")
    }
  }

  test("BigInt Division by Zero", Integers) { ctx =>
    checkPartial(ctx, PartialOperation(Seq(int, int), binary(Division(_, _)), intZero, differs = true))
  }

  test("BigInt Remainder by Zero", Integers) { ctx =>
    checkPartial(ctx, PartialOperation(Seq(int, int), binary(Remainder(_, _)), intZero, differs = true))
  }

  test("BigInt Modulo by Zero", Integers) { ctx =>
    checkPartial(ctx, PartialOperation(Seq(int, int), binary(Modulo(_, _)), intZero, differs = true))
  }

  test("Real Division by Zero", Reals) { ctx =>
    checkPartial(ctx, PartialOperation(Seq(real, real), binary(Division(_, _)), realZero, differs = true))
  }

  test("Selector of Another Constructor", ADTs, Integers) { ctx =>
    val list = T(listID)()
    checkPartial(ctx, PartialOperation(Seq(list), { case Seq(l) => ADTSelector(l, headID) },
      { case Seq(l) => IsConstructor(l, nilID) }, differs = false))
  }

  test("Floating Point Conversion of NaN to Real", FloatingPoint, Reals) { ctx =>
    checkPartial(ctx, PartialOperation(Seq(FPType(11, 53)), { case Seq(f) => FPToReal(f) },
      { case Seq(f) => FPIsNaN(f) }, differs = false))
  }

  test("Floating Point Conversion of Infinity to Real", FloatingPoint, Reals) { ctx =>
    // the two infinities may convert to different reals
    checkPartial(ctx, PartialOperation(Seq(FPType(8, 24)), { case Seq(f) => FPToReal(f) },
      { case Seq(f) => FPIsInfinite(f) }, differs = true))
  }

  test("Partial Operations under Lambdas", Functions, Integers) { ctx =>
    // A lambda whose body fails is a value, and only its applications fail
    val y = Variable.fresh("y", int)
    val f = ValDef.fresh("f", int =>: int)
    val x = ValDef.fresh("x", int)
    def withLambda(body: Expr): Expr =
      Implies(Equals(y, IntegerLiteral(0)), Let(f, Lambda(Seq(x), Division(x.toVariable, y)), body))
    val applied = Application(f.toVariable, Seq(IntegerLiteral(1)))

    val s = solver(ctx)
    assert(s.solveVALID(withLambda(BooleanLiteral(false))) contains false,
      "a lambda that fails when applied should be a value")
    assert(s.solveVALID(withLambda(Equals(applied, IntegerLiteral(2)))) contains true,
      "by default, applying a lambda that fails should be infeasible")

    val cs = solver(ctx.withOpts(optAssumeChecked(true)))
    assert(cs.solveVALID(withLambda(Equals(applied, IntegerLiteral(2)))) contains false,
      "under assume-checked, applying a lambda that would fail should have some value")
    assert(cs.solveVALID(withLambda(Equals(applied, Division(IntegerLiteral(1), y)))) contains true,
      "under assume-checked, applying a lambda should agree with its body")
  }
}
