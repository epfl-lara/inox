/* Copyright 2009-2024 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.Tag

class InvariantSolverSuite extends AnyFunSuite {
  import inox.trees._
  import dsl._

  val ctx = TestContext.empty
  val p = InoxProgram(NoSymbols)

  val solverOpts = List(
    (() => SolverFactory.hasZ3, "inv-z3"),
    (() => true, "inv-eld"),
  )

  val solverNames = solverOpts.flatMap {case (cond, name) => if cond() then List(name) else Nil}

  def getSolver(ctx: Context) =
    SimpleSolverAPI(p.getSolver(ctx))

  // sum(n) = if (n <= 0) 0 else n + sum(n - 1)
  val sumID = FreshIdentifier("sum")
  val sumFd = mkFunDef(sumID)() { _ =>
    (Seq("n" :: IntegerType()), IntegerType(), { case Seq(n) =>
      if_ (n <= E(BigInt(0))) {
        E(BigInt(0))
      } else_ {
        n + E(sumID)(n - E(BigInt(1)))
      }
    })
  }

  // inc(n) = { assume(n >= 0); val m = n + 1; m }
  val incID = FreshIdentifier("inc")
  val incFd = mkFunDef(incID)() { _ =>
    (Seq("n" :: IntegerType()), IntegerType(), { case Seq(n) =>
      Assume(n >= E(BigInt(0)), let("m" :: IntegerType(), n + E(BigInt(1)))(m => m))
    })
  }

  // twice(n) = sum(n) + sum(n)
  val twiceID = FreshIdentifier("twice")
  val twiceFd = mkFunDef(twiceID)() { _ =>
    (Seq("n" :: IntegerType()), IntegerType(), { case Seq(n) => E(sumID)(n) + E(sumID)(n) })
  }

  val fp = InoxProgram(NoSymbols.withFunctions(Seq(sumFd, incFd, twiceFd)))

  def getFunSolver(ctx: Context) =
    SimpleSolverAPI(fp.getSolver(ctx).withTimeout(scala.concurrent.duration.Duration(60, "s")))

  def assertValid(ctx: Context, e: Expr): Unit =
    assert(getFunSolver(ctx).solveVALID(e) == Some(true), s"$e should be valid")

  def assertInvalid(ctx: Context, e: Expr): Unit =
    assert(getFunSolver(ctx).solveVALID(e) == Some(false), s"$e should be invalid")

  /** Registers a test that the solvers fail because of a known bug, as ignored. */
  protected def knownIssue(name: String, reason: String)(body: Context => Unit): Unit = {
    for
      sname <- solverNames
      ctx = TestContext(Options(Seq(optSelectedSolvers(Set(sname)))))
    do
      super.ignore(s"$name ($sname) (known issue: $reason)") {
        body(ctx)
      }
  }

  protected def test(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    for
      sname <- solverNames
      ctx = TestContext(Options(Seq(optSelectedSolvers(Set(sname)))))
    do
      super.test(s"$name ($sname)", tags*) {
        body(ctx)
      }
  }

  test("Validity of true") { ctx =>
    val solver = getSolver(ctx)
    solver.solveVALID(BooleanLiteral(true)) match {
      case Some(true) => ()
      case Some(false) => fail("True is not valid")
      case None => fail("Solver returned unknown")
    }
  }

  test("Unsatisfiability of false") { ctx =>
    val solver = getSolver(ctx)
    solver.solveSAT(BooleanLiteral(false)) match {
      case SolverResponses.Unsat => ()
      case SolverResponses.SatWithModel(_) => fail("False is not invalid")
      case _ => fail("Solver returned unknown response")
    }
  }

  test("Integer arithmetic") { ctx =>
    val solver = getSolver(ctx)
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    val z = Variable.fresh("z", IntegerType())

    val eqs = List(
      x === y + z,
      y === IntegerLiteral(1),
      z === IntegerLiteral(2)
    )

    solver.solveSAT(andJoin(eqs)) match {
      case SolverResponses.SatWithModel(model) => ()
      case SolverResponses.Unsat => fail("Trivial integer arithmetic is unsat")
      case _ => fail("Solver returned unknown response")
    }
  }

  test("Unsatisfiable boolean structure") { ctx =>
    val solver = getSolver(ctx)
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    val e = And(Or(x < y, x === y), Not(x <= y))
    assert(solver.solveSAT(e).isUNSAT)
    assert(solver.solveSAT(Or(e, x > y)).isSAT)
  }

  test("Invariant of a recursive function") { ctx =>
    val x = Variable.fresh("x", IntegerType())
    assertValid(ctx, E(sumID)(x) >= E(BigInt(0)))
    assertValid(ctx, E(sumID)(x) >= x)
    assertInvalid(ctx, E(sumID)(x) > x)
  }

  test("Functions calling functions") { ctx =>
    val x = Variable.fresh("x", IntegerType())
    assertValid(ctx, E(twiceID)(x) >= E(BigInt(0)))
    assertInvalid(ctx, E(twiceID)(x) > E(BigInt(0)))
  }

  test("Functions with assumptions and bindings") { ctx =>
    val x = Variable.fresh("x", IntegerType())
    assertValid(ctx, Implies(x >= E(BigInt(0)), E(incID)(x) > x))
    assertValid(ctx, Implies(x >= E(BigInt(0)), E(incID)(E(incID)(x)) === x + E(BigInt(2))))
    assertInvalid(ctx, Implies(x >= E(BigInt(0)), E(incID)(x) === x))
  }

  knownIssue("Conditionals", "if-expressions are encoded with predicates of the wrong arity") { ctx =>
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    assertValid(ctx, if_ (x > y) { x } else_ { y } >= x)
    assertInvalid(ctx, if_ (x > y) { x } else_ { y } > x)
  }

  test("Bindings") { ctx =>
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    assertValid(ctx, let("z" :: IntegerType(), x + y)(z => z - y === x))
    assertInvalid(ctx, let("z" :: IntegerType(), x + y)(z => z === x))
  }

  knownIssue("Assumptions in the checked formula", "fails an assertion that formulas have no assumptions") { ctx =>
    val x = Variable.fresh("x", IntegerType())
    assertValid(ctx, Assume(x > E(BigInt(0)), x + x > x))
    assertValid(ctx, Assume(E(sumID)(x) > E(BigInt(0)), x > E(BigInt(0))))
  }

  knownIssue("Lambdas and applications", "lambdas reach the underlying Horn solver, which doesn't support them") { ctx =>
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    val inc = \("a" :: IntegerType())(a => a + E(BigInt(1)))
    assertValid(ctx, Application(inc, Seq(x)) > x)
    assertValid(ctx, let("f" :: FunctionType(Seq(IntegerType()), IntegerType()), inc)(f => f(x) > x))
    assertInvalid(ctx, let("f" :: FunctionType(Seq(IntegerType()), IntegerType()), inc)(f => f(x) === f(y)))
  }

  knownIssue("Chooses", "chooses aren't implemented") { ctx =>
    val x = Variable.fresh("x", IntegerType())
    assertValid(ctx, choose("r" :: IntegerType())(r => r > x) > x)
    assertInvalid(ctx, choose("r" :: IntegerType())(r => r > x) === x + E(BigInt(1)))
  }

  knownIssue("Incremental constraints", "the clauses of earlier checks stay asserted in the Horn solver") { ctx =>
    val x = Variable.fresh("x", IntegerType())
    val solver = fp.getSolver(ctx).getNewSolver()
    try {
      solver.assertCnstr(E(sumID)(x) === E(BigInt(3)))
      assert(solver.check(SolverResponses.Simple).isSAT)
      solver.push()
      solver.assertCnstr(x < E(BigInt(0)))
      assert(solver.check(SolverResponses.Simple).isUNSAT)
      solver.pop()
      assert(solver.checkAssumptions(SolverResponses.Simple)(Set(x > E(BigInt(1)))).isSAT)
      solver.reset()
      assert(solver.check(SolverResponses.Simple).isSAT)
    } finally {
      solver.free()
    }
  }
}
