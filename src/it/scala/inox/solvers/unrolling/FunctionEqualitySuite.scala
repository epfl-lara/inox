/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

class FunctionEqualitySuite extends SolvingTestSuite with DatastructureUtils {
  import inox.trees._
  import dsl._

  val f = FreshIdentifier("f")
  val mmapID = FreshIdentifier("MMap")
  val mmap = mkConstructor(mmapID)("A","B")(None) {
    case Seq(aT, bT) => Seq(ValDef(f, aT =>: T(optionID)(bT)))
  }

  val containsID = FreshIdentifier("contains")
  val contains = mkFunDef(containsID)("A", "B") { case Seq(aT, bT) => (
    Seq("m" :: T(mmapID)(aT, bT), "k" :: aT), BooleanType, { case Seq(m, k) =>
      m.getField(f)(k).isInstOf(T(someID)(bT))
    })
  }

  val symbols = baseSymbols
    .withFunctions(Seq(contains))
    .withADTs(Seq(mmap))

  val program = InoxProgram(symbols)

  test("simple theorem") { implicit ctx =>
    val clause = let(
      "states" :: T(mmapID)(IntegerType, IntegerType =>: IntegerType),
      T(mmapID)(IntegerType, IntegerType =>: IntegerType)(\("i" :: IntegerType)(i => T(someID)(IntegerType =>: IntegerType)(\("x" :: IntegerType)(x => IntegerLiteral(0)))))
    )(states => contains(IntegerType, IntegerType =>: IntegerType)(states, IntegerLiteral(0)) && E(false))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(clause)).isSAT)
  }

  test("possible equality 1") { implicit ctx =>
    val f = ("f" :: (IntegerType =>: IntegerType)).toVariable
    val g = ("g" :: (IntegerType =>: IntegerType)).toVariable
    val clause = f === (\("x" :: IntegerType)(x => g(x)))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("possible equality 2") { implicit ctx =>
    val f = ("f" :: (IntegerType =>: IntegerType)).toVariable
    val g = ("g" :: (IntegerType =>: IntegerType)).toVariable
    val clause = g === (\("x" :: IntegerType)(x => f(x)))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("impossible equality 1") { implicit ctx =>
    val f = ("f" :: (IntegerType =>: IntegerType)).toVariable
    val clause = f === (\("x" :: IntegerType)(x => f(x)))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  test("impossible equality 2") { implicit ctx =>
    val f = ("f" :: (IntegerType =>: IntegerType)).toVariable
    val g = ("g" :: (IntegerType =>: IntegerType)).toVariable
    val clause = f === (\("x" :: IntegerType)(x => g(x))) && g === (\("x" :: IntegerType)(x => f(x)))

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }
}
