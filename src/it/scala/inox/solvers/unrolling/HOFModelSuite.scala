/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import SolverResponses._

/** Checks that models of higher-order free functions can be extracted and validated.
  *
  * Princess is left out: its models evaluate every application of a higher-order free
  * function to the same value, so they fail validation.
  */
class HOFModelSuite extends SolvingTestSuite {
  import inox.trees._
  import dsl._

  override def configurations =
    for {
      solverName   <- Seq("nativez3", "unrollz3", "smt-z3", "smt-cvc4", "smt-cvc5")
      modelFinding <- Seq(0, 1)
    } yield Seq(
      optSelectedSolvers(Set(solverName)),
      optCheckModels(true),
      optModelFinding(modelFinding),
      optTimeout(300),
    )

  override def optionsString(options: Options): String =
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "model=" + options.findOptionOrDefault(optModelFinding)

  val program = InoxProgram(NoSymbols)

  private def assertSAT(clause: Expr)(using Context): Unit = {
    SimpleSolverAPI(program.getSolver).solveSAT(clause) match {
      case SatWithModel(_) =>
      case res => fail(s"Expected a model, got $res")
    }
  }

  val I = IntegerType()

  test("higher-order free function applied to free functions") {
    val f = ("f" :: ((I =>: I) =>: I)).toVariable
    val g = ("g" :: (I =>: I)).toVariable
    val h = ("h" :: (I =>: I)).toVariable
    assertSAT(f(g) === E(BigInt(1)) && f(h) === E(BigInt(2)))
  }

  test("higher-order free function applied to lambdas") {
    val f = ("f" :: ((I =>: I) =>: I)).toVariable
    val l1 = \("x" :: I)(x => x + E(BigInt(1)))
    val l2 = \("x" :: I)(x => x + E(BigInt(2)))
    assertSAT(f(l1) === E(BigInt(1)) && f(l2) === E(BigInt(2)))
  }

  test("higher-order free function applied to constrained functions") {
    val f = ("f" :: ((I =>: I) =>: I)).toVariable
    val g = ("g" :: (I =>: I)).toVariable
    val h = ("h" :: (I =>: I)).toVariable
    assertSAT(
      f(g) === E(BigInt(1)) && f(h) === E(BigInt(2)) &&
      g(E(BigInt(0))) === E(BigInt(5)) && h(E(BigInt(0))) === E(BigInt(6)))
  }

  test("higher-order free function with two function parameters") {
    val f = ("f" :: ((I =>: I, I =>: I) =>: I)).toVariable
    val g = ("g" :: (I =>: I)).toVariable
    val h = ("h" :: (I =>: I)).toVariable
    assertSAT(f(g, h) === E(BigInt(1)) && f(h, g) === E(BigInt(2)))
  }
}
