/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** The return type of a function only holds for arguments in its parameter types (Voirol,
  * EPFL thesis 9479, §3.6), so it must not be assumed at calls with ill-typed arguments.
  */
class CallArgumentTypeSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  private def zero = refinement("y" :: IntegerType())(_ === E(BigInt(0)))
  private def pos = refinement("y" :: IntegerType())(_ > E(BigInt(0)))

  // def id0(x: {y | y == 0}): {y | y == 0} = x
  private val id0ID = FreshIdentifier("id0")
  private val id0 = mkFunDef(id0ID)() { _ => (Seq("x" :: zero), zero, { case Seq(x) => x }) }

  // def count(n: {y | y > 0}): {y | y > 0} = if (n == 1) 1 else count(n - 1) + 1
  private val countID = FreshIdentifier("count")
  private val count = mkFunDef(countID)() { _ => (Seq("n" :: pos), pos, { case Seq(n) =>
    if_ (n === E(BigInt(1))) { E(BigInt(1)) } else_ { FunctionInvocation(countID, Seq(), Seq(n - E(BigInt(1)))) + E(BigInt(1)) }
  }) }

  override protected def symbols: Symbols = NoSymbols.withFunctions(Seq(id0, count))
  given Symbols = symbols

  override protected def options = Seq(optCheckModels(true))

  test("return type is not assumed for ill-typed arguments", Integers) { ctx =>
    val s = solver(ctx)
    // id0(1) evaluates to 1
    val res = s.solveSAT(Not(FunctionInvocation(id0ID, Seq(), Seq(E(BigInt(1)))) === E(BigInt(0))))
    assert(res.isSAT, s"expected SAT, got $res")
  }

  test("return type is assumed for well-typed arguments", Integers) { ctx =>
    val s = solver(ctx)
    val res = s.solveSAT(Not(FunctionInvocation(id0ID, Seq(), Seq(E(BigInt(0)))) === E(BigInt(0))))
    assert(res.isUNSAT, s"expected UNSAT, got $res")
  }

  test("return type is assumed for arguments typed by their context", Integers) { ctx =>
    val s = solver(ctx)
    val x = Variable.fresh("x", pos)
    val res = s.solveSAT(Not(FunctionInvocation(countID, Seq(), Seq(x)) > E(BigInt(0))))
    assert(res.isUNSAT, s"expected UNSAT, got $res")
  }

  test("return type is assumed for ill-typed arguments under assume-checked", Integers) { ctx =>
    val s = solver(ctx.withOpts(optAssumeChecked(true)))
    // the front-end has checked the arguments of every call, so id0(1) is assumed to be 0
    val res = s.solveSAT(Not(FunctionInvocation(id0ID, Seq(), Seq(E(BigInt(1)))) === E(BigInt(0))))
    assert(res.isUNSAT, s"expected UNSAT, got $res")
  }
}
