/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

class ChooseSuite extends SolvingTestSuite {
  import trees._
  import dsl._

  override def configurations =
    for (nme <- Seq("nativez3", "unrollz3", "smt-z3", "smt-cvc4", "princess")) yield {
      Seq(optSelectedSolvers(Set(nme)), optCheckModels(true))
    }

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  // Simple functions that contains a choose
  val fun1 = mkFunDef(FreshIdentifier("fun1"))()(_ => (
    Seq("x" :: IntegerType), IntegerType, { case Seq(x) =>
      if_ (x <= E(BigInt(0))) {
        choose("v" :: IntegerType)(_ > E(BigInt(0)))
      } else_ {
        x
      }
    }))

  // Function that contains a choose AND calls another function containing a choose
  val fun2 = mkFunDef(FreshIdentifier("fun2"))()(_ => (
    Seq("x" :: IntegerType, "y" :: IntegerType), IntegerType, { case Seq(x, y) =>
      if_ (x <= E(BigInt(0))) {
        choose("v" :: IntegerType)(_ > E(BigInt(0)))
      } else_ {
        fun1(y)
      }
    }))

  // Function containing a choose that depends on a type parameter
  val fun3 = mkFunDef(FreshIdentifier("fun3"))("T") { case Seq(aT) => (
    Seq("x" :: aT, "b" :: BooleanType), aT, { case Seq(x, b) =>
      if_ (b) {
        choose("v" :: aT)(_ => E(true))
      } else_ {
        x
      }
    })
  }

  // Recursive function where the same choose takes on different values
  val fun4ID = FreshIdentifier("fun4")
  val fun4 = mkFunDef(fun4ID)()(_ => (
    Seq("x" :: IntegerType, "y" :: IntegerType), IntegerType, { case Seq(x, y) =>
      if_ (x >= E(BigInt(0))) {
        choose("v" :: IntegerType)(_ > y) + E(fun4ID)(x - E(BigInt(1)), y - E(BigInt(1)))
      } else_ {
        E(BigInt(0))
      }
    }))

  val symbols = NoSymbols.withFunctions(Seq(fun1, fun2, fun3, fun4))
  val program = InoxProgram(symbols)

  test("simple choose") { implicit ctx =>
    val clause = choose("v" :: IntegerType)(v => v > IntegerLiteral(0)) === IntegerLiteral(10)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("choose in function") { implicit ctx =>
    val clause = fun1(IntegerLiteral(-1)) === IntegerLiteral(10)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("choose in function and arguments") { implicit ctx =>
    val clause = fun1(choose("v" :: IntegerType)(_ < IntegerLiteral(0))) === IntegerLiteral(10)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("choose in callee function") { implicit ctx =>
    val clause = fun2(IntegerLiteral(1), IntegerLiteral(-1)) === IntegerLiteral(10) &&
      fun2(IntegerLiteral(-1), IntegerLiteral(0)) === IntegerLiteral(2)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("choose in parametric function") { implicit ctx =>
    val clause = fun3(IntegerType)(IntegerLiteral(1), E(true)) === IntegerLiteral(10) &&
      fun3(BooleanType)(E(true), E(true)) === E(false)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("choose in recursive function") { implicit ctx =>
    val clause = fun4(IntegerLiteral(2), IntegerLiteral(1)) === IntegerLiteral(10)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)

    val clause2 = fun4(IntegerLiteral(2), IntegerLiteral(2)) === IntegerLiteral(6)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause2).isSAT)

    val clause3 = fun4(IntegerLiteral(2), IntegerLiteral(2)) === IntegerLiteral(5)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause3).isUNSAT)
  }
}
