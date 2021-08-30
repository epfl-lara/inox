/* Copyright 2009-2020 EPFL, Lausanne */

package inox
package solvers
package unrolling

class MapEqualValueKeysSuite extends SolvingTestSuite with DatastructureUtils {
  import trees._
  import dsl._

  override def configurations = for {
    // FIXME(gsps): The native z3 version we use is old and yields unsound models.
    // solverName   <- Seq("nativez3", "unrollz3", "smt-z3")
    solverName   <- Seq("smt-z3")
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

  val map1 = ("map1" :: MapType(keyT, valueT)).toVariable
  val map2 = ("map2" :: MapType(keyT, valueT)).toVariable
  val equalKeys = MapEqualValueKeys(map1, map2)
  val someKey = ("someKey" :: keyT).toVariable
  val someValue1 = ("someValue1" :: valueT).toVariable
  val someValue2 = ("someValue2" :: valueT).toVariable

  val symbols = baseSymbols
  val program = InoxProgram(symbols)

  test("Finite model finding 1") { implicit ctx =>
    val clause = Equals(equalKeys, FiniteSet(Seq.empty, keyT))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Finite model finding 2") { implicit ctx =>
    val clause = Equals(equalKeys, FiniteSet(Seq(someKey), keyT))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Minimal empty result set example") { implicit ctx =>
    val clause = Implies(
      and(
        Equals(map1, FiniteMap(Seq.empty, someValue1, keyT, valueT)),
        Equals(map2, FiniteMap(Seq.empty, someValue2, keyT, valueT)),
        Not(Equals(someValue1, someValue2))),
      Equals(equalKeys, FiniteSet(Seq.empty, keyT)))
    assert(SimpleSolverAPI(program.getSolver).solveVALID(clause) contains true)
  }

  test("Equally-valued key is in result set") { implicit ctx =>
    val clause = Implies(
      Equals(MapApply(map1, someKey), MapApply(map2, someKey)),
      ElementOfSet(someKey, equalKeys))
    assert(SimpleSolverAPI(program.getSolver).solveVALID(clause) contains true)
  }
}
