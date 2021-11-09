/* Copyright 2009-2020 EPFL, Lausanne */

package inox
package solvers
package unrolling

class MapMergeSuite extends SolvingTestSuite with DatastructureUtils {
  import trees._
  import dsl._

  override def configurations = for {
    solverName   <- Seq("nativez3", "unrollz3", "smt-z3")
    feelingLucky <- Seq(false, true)
  } yield Seq(
    optSelectedSolvers(Set(solverName)),
    optCheckModels(true),
    optFeelingLucky(feelingLucky),
    optTimeout(300),
    ast.optPrintUniqueIds(true)
  )

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(optFeelingLucky)
  }

  val keyT = TypeParameter.fresh("K")
  val valueT = TypeParameter.fresh("V")

  val mask = ("mask" :: SetType(keyT)).toVariable
  val map1 = ("map1" :: MapType(keyT, valueT)).toVariable
  val map2 = ("map2" :: MapType(keyT, valueT)).toVariable
  val merged = MapMerge(mask, map1, map2)
  val dummyValue = ("dummyValue" :: valueT).toVariable
  val someKey = ("someKey" :: keyT).toVariable

  val symbols = baseSymbols
  val program = InoxProgram(symbols)

  test("Finite model finding 1") {
    val clause = Not(Equals(merged, FiniteMap(Seq.empty, dummyValue, keyT, valueT)))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Finite model finding 2") {
    val clause = Not(Equals(merged, map1))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Finite model finding 3") {
    val clause = Not(Equals(merged, map2))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Empty mask") {
    val clause = Implies(Equals(mask, FiniteSet(Seq.empty, keyT)), Equals(merged, map2))
    assert(SimpleSolverAPI(program.getSolver).solveVALID(clause) contains true)
  }

  test("Element in mask") {
    val clause = Implies(
      ElementOfSet(someKey, mask),
      Equals(MapApply(merged, someKey), MapApply(map1, someKey)))
    assert(SimpleSolverAPI(program.getSolver).solveVALID(clause) contains true)
  }
}
