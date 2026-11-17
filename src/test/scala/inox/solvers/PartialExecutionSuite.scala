/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Functions that fail or diverge on some inputs (see `unrolling/partial-execution.md`).
  *
  * A query holds when it evaluates to `true`, so evaluation that fails or diverges never makes it
  * hold. A function `f` lies in `Pi(x: A). B` when `f(a)` lies in `B` whenever it returns a value.
  * Neither the solver nor the evaluator establishes that a call diverges, so the queries whose
  * answer depends on it are undecided. */
class PartialExecutionSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  // def loop(x: BigInt): BigInt = loop(x)
  val loopID = FreshIdentifier("loop")
  val loopFd = mkFunDef(loopID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => E(loopID)(x) }) }

  // def loopPos(x: BigInt): BigInt = if (x > 0) loopPos(x) else x
  val loopPosID = FreshIdentifier("loopPos")
  val loopPosFd = mkFunDef(loopPosID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
    if_(x > E(BigInt(0))) { E(loopPosID)(x) } else_ { x }
  }) }

  // def loopPlusOne(x: BigInt): BigInt = loopPlusOne(x) + 1
  val loopPlusOneID = FreshIdentifier("loopPlusOne")
  val loopPlusOneFd = mkFunDef(loopPlusOneID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
    E(loopPlusOneID)(x) + E(BigInt(1))
  }) }

  // def ping(x: BigInt): BigInt = if (x > 0) pong(x) else x
  // def pong(x: BigInt): BigInt = ping(x)
  val pingID = FreshIdentifier("ping")
  val pongID = FreshIdentifier("pong")
  val pingFd = mkFunDef(pingID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
    if_(x > E(BigInt(0))) { E(pongID)(x) } else_ { x }
  }) }
  val pongFd = mkFunDef(pongID)() { _ => (Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => E(pingID)(x) }) }

  override protected def symbols: Symbols =
    NoSymbols.withFunctions(Seq(loopFd, loopPosFd, loopPlusOneFd, pingFd, pongFd))
  given Symbols = symbols

  override protected def options = Seq(optCheckModels(true))

  private def unsat(e: Expr)(using ctx: Context): Unit = {
    val res = solver(ctx).solveSAT(e)
    assert(res.isUNSAT, s"expected UNSAT, got $res")
  }
  private def sat(e: Expr)(using ctx: Context): Unit = {
    val res = solver(ctx).solveSAT(e)
    assert(res.isSAT, s"expected SAT, got $res")
  }

  private def unknown(e: Expr)(using ctx: Context): Unit = {
    val res = solver(ctx).solveSAT(e)
    assert(!res.isSAT && !res.isUNSAT, s"expected unknown, got $res")
  }

  private val k = Variable.fresh("k", IntegerType())

  test("a call that reaches itself isn't shown to diverge", Integers) { ctx =>
    unknown(E(loopID)(k) === E(BigInt(0)))(using ctx)
  }
  test("a call that reaches itself on some inputs only returns on the others", Integers) { ctx =>
    unknown(E(loopPosID)(k) === E(BigInt(5)))(using ctx)
    sat(E(loopPosID)(k) === E(BigInt(0)))(using ctx)
  }
  test("a call that reaches itself through another function only returns off the cycle", Integers) { ctx =>
    unknown(E(pingID)(k) === E(BigInt(5)))(using ctx)
    unknown(E(pongID)(k) === E(BigInt(5)))(using ctx)
    sat(E(pingID)(k) === E(BigInt(0)))(using ctx)
  }
  test("a call whose unfolding is contradictory never returns", Integers) { ctx =>
    unsat(E(loopPlusOneID)(k) === E(BigInt(0)))(using ctx)
  }

  // h: (BigInt => {v: BigInt | v > 0}) => {b: Boolean | b}, so !h(g) is UNSAT iff g lies in h's domain
  private val posVd = "v" :: IntegerType()
  private val pos = RefinementType(posVd, posVd.toVariable > E(BigInt(0)))
  private def inDomain(g: Expr)(using Context): Unit = {
    val bVd = "b" :: BooleanType()
    val h = Variable.fresh("h", FunctionType(Seq(IntegerType() =>: pos), RefinementType(bVd, bVd.toVariable)))
    unsat(Not(Application(h, Seq(g))))
  }
  private def notInDomain(g: Expr)(using ctx: Context): Unit = {
    val bVd = "b" :: BooleanType()
    val h = Variable.fresh("h", FunctionType(Seq(IntegerType() =>: pos), RefinementType(bVd, bVd.toVariable)))
    val res = solver(ctx).solveSAT(Not(Application(h, Seq(g))))
    assert(!res.isUNSAT, s"expected SAT or unknown, got $res")
  }

  test("a function that fails lies in every function type", Functions, Integers) { ctx =>
    inDomain(\("x" :: IntegerType())(_ => Error(IntegerType(), "stuck")))(using ctx)
  }
  test("a function that diverges isn't shown to lie in a function type", Functions, Integers) { ctx =>
    notInDomain(\("x" :: IntegerType())(x => E(loopID)(x)))(using ctx)
  }
  test("a function lies in a type if its results do where it returns", Functions, Integers) { ctx =>
    inDomain(\("x" :: IntegerType())(x => if_(x > E(BigInt(0))) { x } else_ { Error(IntegerType(), "stuck") }))(using ctx)
  }
  test("a function that returns a value outside of the type doesn't lie in it", Functions, Integers) { ctx =>
    notInDomain(\("x" :: IntegerType())(x => if_(x > E(BigInt(0))) { x } else_ { E(BigInt(0)) }))(using ctx)
  }
}
