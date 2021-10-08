/* Copyright 2009-2020 EPFL, Lausanne */

package inox
package solvers
package unrolling

import scala.language.existentials

import SolverResponses._

class SetBagMapSuite extends SolvingTestSuite with DatastructureUtils {
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

  val symbols = baseSymbols
  val program = InoxProgram(symbols)

  // Tests for Sets

  val x = "x" :: IntegerType()
  val intRefinement = RefinementType(x, GreaterThan(x.toVariable, IntegerLiteral(2000)))
  val emptyType = RefinementType(x, BooleanLiteral(false))

  val s1 = ("s" :: SetType(IntegerType())).toVariable
  val s2 = ("s" :: SetType(intRefinement)).toVariable
  val s3 = ("s" :: SetType(emptyType)).toVariable

  test("Non-empty set") {
    val clause = Not(Equals(s1, FiniteSet(Seq.empty, IntegerType())))
    val SatWithModel(model) = SimpleSolverAPI(program.getSolver).solveSAT(clause)
    val FiniteSet(value1, _) = model.vars(s1.toVal)
    assert(!value1.isEmpty)
  }

  test("Non-empty set with refinement") {
    val clause = Not(Equals(s2, FiniteSet(Seq.empty, IntegerType())))
    val SatWithModel(model) = SimpleSolverAPI(program.getSolver).solveSAT(clause)
    val FiniteSet(Seq(IntegerLiteral(value2)), _) = model.vars(s2.toVal)
    assert(value2 > 2000)
  }

  test("Sets with empty base type are empty") {
    val clause = Equals(s3, FiniteSet(Seq.empty, IntegerType()))
    val result = SimpleSolverAPI(program.getSolver).solveVALID(clause)
    assert(result == Some(true))
  }

  // Tests for Bags

  val bag1 = ("bag" :: BagType(IntegerType())).toVariable

  val y2 = "y" :: IntegerType()
  val bag2 = ("bag" :: BagType(intRefinement)).toVariable

  val y3 = "y" :: IntegerType()
  val bag3 = ("bag" :: BagType(emptyType)).toVariable

  test("Non-empty bag") {
    val clause = Not(Equals(bag1, FiniteBag(Seq.empty, IntegerType())))
    val SatWithModel(model) = SimpleSolverAPI(program.getSolver).solveSAT(clause)
    val FiniteBag(value1, _) = model.vars(bag1.toVal)
    assert(!value1.isEmpty)
  }

  test("Non-empty bag with refinement") {
    val clause = Not(Equals(bag2, FiniteBag(Seq.empty, IntegerType())))
    val SatWithModel(model) = SimpleSolverAPI(program.getSolver).solveSAT(clause)
    val FiniteBag(Seq((IntegerLiteral(value2), _)), _) = model.vars(bag2.toVal)
    assert(value2 > 2000)
  }

  test("Bags with empty base type are empty") {
    val clause = Equals(bag3, FiniteBag(Seq.empty, IntegerType()))
    val result = SimpleSolverAPI(program.getSolver).solveVALID(clause)
    assert(result == Some(true))
  }

  // Tests for Maps

  val map1 = ("map" :: MapType(intRefinement, intRefinement)).toVariable
  val map2 = ("map" :: MapType(emptyType, IntegerType())).toVariable
  val map3 = ("map" :: MapType(IntegerType(), emptyType)).toVariable

  test("Maps with refinement types exist") {
    val clause = Equals(map1, map1)
    val SatWithModel(model) = SimpleSolverAPI(program.getSolver).solveSAT(clause)
    val FiniteMap(_, IntegerLiteral(value), _, _) = model.vars(map1.toVal)
    assert(value > 2000)
  }

  test("Maps with empty key type exist") {
    val clause = Equals(map2, map2)
    val result = SimpleSolverAPI(program.getSolver).solveSAT(clause)
    assert(result.isSAT)
  }

  test("Maps with empty value type don't exist") {
    val clause = Equals(map3, map3)
    val result = SimpleSolverAPI(program.getSolver).solveSAT(clause)
    assert(!result.isSAT)
  }
}
