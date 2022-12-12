/* Copyright 2009-2022 EPFL, Lausanne */

package inox
package solvers
package unrolling

class BVArithmeticSuite extends SolvingTestSuite {
  import trees._
  import dsl._

  import SolverResponses._

  override def configurations = for {
    solverName  <- Seq("nativez3", "unrollz3", "smt-z3", "smt-cvc4", "princess")
  } yield Seq(
    optSelectedSolvers(Set(solverName)),
    optCheckModels(true)
  )

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  val program = InoxProgram(NoSymbols)
  object UInt32Type extends BVTypeExtractor(false, 32)
  val zeroInt32 = BVLiteral(true, 0, 32)
  val zeroUInt32 = BVLiteral(false, 0, 32)

  test("Signed overflow (addition)") {
    val x = Variable.fresh("x", Int32Type())
    val y = Variable.fresh("y", Int32Type())
    val clause = x > zeroInt32 && y > zeroInt32 && x + y < zeroInt32
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Unsigned overflow (addition)") {
    val x = Variable.fresh("x", UInt32Type())
    val y = Variable.fresh("y", UInt32Type())
    val clause = x + y < x
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Signed overflow (subtraction)") {
    val x = Variable.fresh("x", Int32Type())
    val y = Variable.fresh("y", Int32Type())
    val clause = x < zeroInt32 && y < zeroInt32 && x - y > zeroInt32
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Unsigned overflow (subtraction)") {
    val x = Variable.fresh("x", UInt32Type())
    val y = Variable.fresh("y", UInt32Type())
    val clause = x - y > x
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Signed associativity") { associativityTest(Int32Type()) }

  test("Unsigned associativity") { associativityTest(UInt32Type()) }

  test("Signed commutativity") { commutativityTest(Int32Type()) }

  test("Unsigned commutativity") { commutativityTest(UInt32Type()) }

  test("Signed distributivity") { distributivityTest(Int32Type()) }

  test("Unsigned distributivity") { distributivityTest(UInt32Type()) }


  private def associativityTest(tpe: Type)(using Context): Unit = {
    val x = Variable.fresh("x", tpe)
    val y = Variable.fresh("y", tpe)
    val z = Variable.fresh("z", tpe)
    val clause: Expr = x + (y + z) !== (x + y) + z
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  private def commutativityTest(tpe: Type)(using Context): Unit = {
    val x = Variable.fresh("x", tpe)
    val y = Variable.fresh("y", tpe)
    val clause: Expr = x + y !== y + x
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  private def distributivityTest(tpe: Type)(using Context): Unit = {
    val x = Variable.fresh("x", tpe)
    val y = Variable.fresh("y", tpe)
    val z = Variable.fresh("z", tpe)
    val clause: Expr = x * (y + z) !== x * y + x * z
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }
}
