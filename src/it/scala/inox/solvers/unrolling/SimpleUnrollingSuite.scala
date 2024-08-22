/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class SimpleUnrollingSuite extends SolvingTestSuite {
  import inox.trees._
  import dsl._

  import SolverResponses._

  val listID = FreshIdentifier("List")
  val consID = FreshIdentifier("Cons")
  val nilID  = FreshIdentifier("Nil")

  val head = FreshIdentifier("head")
  val tail = FreshIdentifier("tail")

  val List = mkSort(listID)("A") {
    case Seq(aT) => Seq(
      (nilID, Seq()),
      (consID, Seq(ValDef(head, aT), ValDef(tail, T(listID)(aT))))
    )
  }

  val sizeID = FreshIdentifier("size")
  val sizeFd = mkFunDef(sizeID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT)), IntegerType(), { case Seq(l) =>
      if_ (l `is` consID) {
        E(BigInt(1)) + E(sizeID)(aT)(l.getField(tail))
      } else_ {
        E(BigInt(0))
      }
    })
  }

  val symbols = new Symbols(
    Map(sizeID -> sizeFd),
    Map(listID -> List)
  )

  val program = InoxProgram(symbols)
  import program._
  import program.symbols.{given, _}

  test("size(x) > 0 is satisfiable") {
    val vd: ValDef = "x" :: T(listID)(IntegerType())
    val clause = sizeFd(IntegerType())(vd.toVariable) > E(BigInt(0))

    SimpleSolverAPI(program.getSolver).solveSAT(clause) match {
      case SatWithModel(model) =>
        model.vars.get(vd) match {
          case Some(ADT(`consID`, Seq(IntegerType()), _)) =>
            // success!!
          case r =>
            fail("Unexpected valuation: " + r)
        }

      case r =>
        fail("Unexpected response: " + r)
    }
  }

  test("size(x) == 0 is satisfiable") {
    val tp = TypeParameter.fresh("A")
    val vd: ValDef = "x" :: T(listID)(tp)
    val clause = sizeFd(tp)(vd.toVariable) === E(BigInt(0))

    SimpleSolverAPI(program.getSolver).solveSAT(clause) match {
      case SatWithModel(model) =>
        model.vars.get(vd) match {
          case Some(ADT(`nilID`, Seq(`tp`), Seq())) =>
            // success!!
          case r =>
            fail("Unexpected valuation: " + r)
        }

      case r =>
        fail("Unexpected response: " + r)
    }
  }

  test("size(x) < 0 is not satisfiable (unknown)") {
    val vd: ValDef = "x" :: T(listID)(IntegerType())
    val clause = sizeFd(IntegerType())(vd.toVariable) < E(BigInt(0))

    assert(!SimpleSolverAPI(program.getSolver.withTimeout(100)).solveSAT(clause).isSAT)
  }

  test("size(x) > size(y) is satisfiable") {
    val x: ValDef = "x" :: T(listID)(IntegerType())
    val y: ValDef = "y" :: T(listID)(IntegerType())
    val clause = sizeFd(IntegerType())(x.toVariable) > sizeFd(IntegerType())(y.toVariable)

    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("simple configuration is sound with quantifiers") {
    val factory = program.getSolver
    val c = Variable.fresh("c", IntegerType())
    val x = Variable.fresh("x", IntegerType())
    val expr = Forall(Seq(x.toVal), And(Equals(c, x), Equals(c, IntegerLiteral(42))))

    for (config <- Seq(Simple, Model)) {
      val solver = factory.getNewSolver()
      try {
        solver.assertCnstr(expr)
        val result = solver.check(config)
        assert(!result.isSAT && !result.isUNSAT, "Result should be unknown")
      } finally {
        factory.reclaim(solver)
      }
    }
  }
}
