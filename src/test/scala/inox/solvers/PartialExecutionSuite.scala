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
  test("a model never relies on a call that reaches itself", Integers) { ctx =>
    given Context = ctx
    // the models are checked, so they must take the paths that don't close a cycle
    sat(Or(k === E(BigInt(5)), E(loopID)(k) === E(BigInt(0))))
    sat(Or(k === E(BigInt(-2)), E(loopPosID)(k) === E(BigInt(5))))
    sat(Or(k === E(BigInt(-2)), E(pingID)(k) === E(BigInt(5))))
    // `||` evaluates its left operand first, which diverges
    unknown(Or(E(loopID)(k) === E(BigInt(0)), k === E(BigInt(5))))
  }
  test("a proof that doesn't depend on a call diverging goes through", Integers) { ctx =>
    given Context = ctx
    unsat(And(E(loopPosID)(k) === E(BigInt(1)), k <= E(BigInt(0))))
    unsat(Not(E(loopPosID)(E(BigInt(-3))) === E(BigInt(-3))))
    unsat(Not(E(pingID)(E(BigInt(-3))) === E(BigInt(-3))))
  }
  test("calls that reach themselves aren't related to each other", Integers) { ctx =>
    given Context = ctx
    unknown(E(loopID)(k) === E(loopID)(k + E(BigInt(1))))
    unknown(Not(E(loopID)(k) === E(loopID)(k + E(BigInt(1)))))
    // a call equals itself, whether it returns or not
    unsat(Not(E(loopID)(k) === E(loopID)(k)))
  }
  test("a call that reaches itself never returns when the front-end has checked totality", Integers) { ctx =>
    given Context = ctx.withOpts(optAssumeChecked(true))
    unsat(E(loopID)(k) === E(BigInt(0)))
    unsat(E(loopPosID)(k) === E(BigInt(5)))
    unsat(E(pingID)(k) === E(BigInt(5)))
    unsat(E(pongID)(k) === E(BigInt(5)))
    sat(E(loopPosID)(k) === E(BigInt(0)))
    sat(Or(k === E(BigInt(5)), E(loopID)(k) === E(BigInt(0))))
    unsat(Or(E(loopID)(k) === E(BigInt(0)), k === E(BigInt(5))))
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
  private def unknownInDomain(g: Expr)(using Context): Unit = {
    val bVd = "b" :: BooleanType()
    val h = Variable.fresh("h", FunctionType(Seq(IntegerType() =>: pos), RefinementType(bVd, bVd.toVariable)))
    unknown(Not(Application(h, Seq(g))))
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
    unknownInDomain(\("x" :: IntegerType())(x => E(loopID)(x)))(using ctx)
    unknownInDomain(\("x" :: IntegerType())(x => if_(x > E(BigInt(0))) { x } else_ { E(loopID)(x) }))(using ctx)
  }
  test("a function that diverges lies in every function type when the front-end has checked totality",
      Functions, Integers) { ctx =>
    given Context = ctx.withOpts(optAssumeChecked(true))
    inDomain(\("x" :: IntegerType())(x => E(loopID)(x)))
    inDomain(\("x" :: IntegerType())(x => if_(x > E(BigInt(0))) { x } else_ { E(loopID)(x) }))
  }

  // Under extensional equality, functions are compared where they fail, but not where they diverge
  private def extensional(ctx: Context): Context =
    ctx.withOpts(unrolling.optFunctionEquality(unrolling.FunctionEquality.Extensional))
  private def fun(body: Expr => Expr): Expr = \("x" :: IntegerType())(body)
  private val loops = fun(x => E(loopID)(x))

  test("a function that diverges is neither equal to nor distinct from one that returns", Functions, Integers) { ctx =>
    given Context = extensional(ctx)
    unknown(Not(Equals(loops, fun(_ => E(BigInt(0))))))
    unknown(Equals(loops, fun(_ => E(BigInt(0)))))
  }
  test("a function that diverges is neither equal to nor distinct from one that fails", Functions, Integers) { ctx =>
    given Context = extensional(ctx)
    unknown(Not(Equals(loops, fun(x => Division(x, E(BigInt(0)))))))
    unknown(Equals(loops, fun(x => Division(x, E(BigInt(0))))))
    unknown(Not(Equals(loops, fun(_ => Error(IntegerType(), "stuck")))))
  }
  test("a free function is neither equal to nor distinct from one that diverges", Functions, Integers) { ctx =>
    given Context = extensional(ctx)
    val f = Variable.fresh("f", IntegerType() =>: IntegerType())
    unknown(Not(Equals(f, loops)))
  }
  test("functions that diverge on some inputs are compared on the others", Functions, Integers) { ctx =>
    given Context = extensional(ctx)
    val loopPos = fun(x => E(loopPosID)(x))
    // they differ on the inputs on which loopPos returns
    sat(Not(Equals(loopPos, fun(_ => E(BigInt(1))))))
    sat(Not(Equals(loopPos, fun(x => if_(x > E(BigInt(0))) { Error(IntegerType(), "stuck") } else_ { x + E(BigInt(1)) }))))
    // they agree on those inputs, and only differ where loopPos diverges
    unknown(Not(Equals(loopPos, fun(x => if_(x > E(BigInt(0))) { E(BigInt(0)) } else_ { x }))))
    unknown(Not(Equals(loopPos, fun(x => if_(x > E(BigInt(0))) { Division(x, E(BigInt(0))) } else_ { x }))))
  }
  test("a function that diverges equals itself", Functions, Integers) { ctx =>
    given Context = extensional(ctx)
    unsat(Not(Equals(loops, loops)))
    unsat(Not(Equals(loops, fun(y => E(loopID)(y)))))
  }
  test("a function lies in a type if its results do where it returns", Functions, Integers) { ctx =>
    inDomain(\("x" :: IntegerType())(x => if_(x > E(BigInt(0))) { x } else_ { Error(IntegerType(), "stuck") }))(using ctx)
  }
  test("a function that returns a value outside of the type doesn't lie in it", Functions, Integers) { ctx =>
    notInDomain(\("x" :: IntegerType())(x => if_(x > E(BigInt(0))) { x } else_ { E(BigInt(0)) }))(using ctx)
  }
}
