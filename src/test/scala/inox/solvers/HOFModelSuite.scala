/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Checks that models of higher-order free functions can be extracted and validated.
  *
  * Princess's models evaluate every application of a higher-order free function to the same
  * value, so they fail validation (see the known issues in [[SolverTestSuite.solvers]]).
  */
class HOFModelSuite extends SolverTestSuite {
  import inox.trees._
  import dsl._
  import SolverResponses._

  override protected def options = Seq(optCheckModels(true))

  private def assertSAT(ctx: Context, clause: Expr): Unit = {
    solver(ctx).solveSAT(clause) match {
      case SatWithModel(_) =>
      case res => fail(s"Expected a model, got $res")
    }
  }

  val I = IntegerType()

  test("higher-order free function applied to free functions", Integers, Functions) { ctx =>
    val f = ("f" :: ((I =>: I) =>: I)).toVariable
    val g = ("g" :: (I =>: I)).toVariable
    val h = ("h" :: (I =>: I)).toVariable
    assertSAT(ctx, f(g) === E(BigInt(1)) && f(h) === E(BigInt(2)))
  }

  test("higher-order free function applied to lambdas", Integers, Functions) { ctx =>
    val f = ("f" :: ((I =>: I) =>: I)).toVariable
    val l1 = \("x" :: I)(x => x + E(BigInt(1)))
    val l2 = \("x" :: I)(x => x + E(BigInt(2)))
    assertSAT(ctx, f(l1) === E(BigInt(1)) && f(l2) === E(BigInt(2)))
  }

  test("higher-order free function applied to constrained functions", Integers, Functions) { ctx =>
    val f = ("f" :: ((I =>: I) =>: I)).toVariable
    val g = ("g" :: (I =>: I)).toVariable
    val h = ("h" :: (I =>: I)).toVariable
    assertSAT(ctx,
      f(g) === E(BigInt(1)) && f(h) === E(BigInt(2)) &&
      g(E(BigInt(0))) === E(BigInt(5)) && h(E(BigInt(0))) === E(BigInt(6)))
  }

  test("higher-order free function with two function parameters", Integers, Functions) { ctx =>
    val f = ("f" :: ((I =>: I, I =>: I) =>: I)).toVariable
    val g = ("g" :: (I =>: I)).toVariable
    val h = ("h" :: (I =>: I)).toVariable
    assertSAT(ctx, f(g, h) === E(BigInt(1)) && f(h, g) === E(BigInt(2)))
  }
}
