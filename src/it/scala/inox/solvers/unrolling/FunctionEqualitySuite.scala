/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

class FunctionEqualitySuite extends SolvingTestSuite {
  import inox.trees._
  import dsl._

  val v = FreshIdentifier("value")

  val optionID = FreshIdentifier("Option")
  val someID = FreshIdentifier("Some")
  val noneID = FreshIdentifier("None")

  val option = mkSort(optionID)("A")(Seq(someID, noneID))
  val none   = mkConstructor(noneID)("A")(Some(optionID))(_ => Seq.empty)
  val some   = mkConstructor(someID)("A")(Some(optionID)) {
    case Seq(aT) => Seq(ValDef(v, aT))
  }

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

  val symbols = new Symbols(
    Map(containsID -> contains),
    Map(optionID -> option, someID -> some, noneID -> none, mmapID -> mmap)
  )

  test("simple theorem") { ctx =>
    val program = InoxProgram(ctx, symbols)
    val clause = let(
      "states" :: T(mmapID)(IntegerType, IntegerType =>: IntegerType),
      T(mmapID)(IntegerType, IntegerType =>: IntegerType)(\("i" :: IntegerType)(i => T(someID)(IntegerType =>: IntegerType)(\("x" :: IntegerType)(x => IntegerLiteral(0)))))
    )(states => contains(IntegerType, IntegerType =>: IntegerType)(states, IntegerLiteral(0)) && E(false))

    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(Not(clause)).isSAT)
  }

  test("possible equality 1") { ctx =>
    val program = InoxProgram(ctx, symbols)
    val f = ("f" :: (IntegerType =>: IntegerType)).toVariable
    val g = ("g" :: (IntegerType =>: IntegerType)).toVariable
    val clause = f === (\("x" :: IntegerType)(x => g(x)))

    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause).isSAT)
  }

  test("possible equality 2") { ctx =>
    val program = InoxProgram(ctx, symbols)
    val f = ("f" :: (IntegerType =>: IntegerType)).toVariable
    val g = ("g" :: (IntegerType =>: IntegerType)).toVariable
    val clause = g === (\("x" :: IntegerType)(x => f(x)))

    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause).isSAT)
  }

  test("impossible equality 1") { ctx =>
    val program = InoxProgram(ctx, symbols)
    val f = ("f" :: (IntegerType =>: IntegerType)).toVariable
    val clause = f === (\("x" :: IntegerType)(x => f(x)))

    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause).isUNSAT)
  }

  test("impossible equality 2") { ctx =>
    val program = InoxProgram(ctx, symbols)
    val f = ("f" :: (IntegerType =>: IntegerType)).toVariable
    val g = ("g" :: (IntegerType =>: IntegerType)).toVariable
    val clause = f === (\("x" :: IntegerType)(x => g(x))) && g === (\("x" :: IntegerType)(x => f(x)))

    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause).isUNSAT)
  }
}
