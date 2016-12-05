/* Copyright 2009-2016 EPFL, Lausanne */

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

  val List = mkSort(listID)("A")(Seq(consID, nilID))
  val Nil  = mkConstructor(nilID)("A")(Some(listID))(_ => Seq.empty)
  val Cons = mkConstructor(consID)("A")(Some(listID)) {
    case Seq(aT) => Seq(ValDef(head, aT), ValDef(tail, T(listID)(aT)))
  }

  val sizeID = FreshIdentifier("size")
  val sizeFd = mkFunDef(sizeID)("A") { case Seq(aT) => (
    Seq("l" :: T(listID)(aT)), IntegerType, { case Seq(l) =>
      if_ (l.isInstOf(T(consID)(aT))) {
        E(BigInt(1)) + E(sizeID)(aT)(l.asInstOf(T(consID)(aT)).getField(tail))
      } else_ {
        E(BigInt(0))
      }
    })
  }

  val symbols = new Symbols(
    Map(sizeID -> sizeFd),
    Map(listID -> List, consID -> Cons, nilID -> Nil)
  )

  test("size(x) > 0 is satisfiable") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val vd: ValDef = "x" :: T(listID)(IntegerType)
    val clause = sizeFd(IntegerType)(vd.toVariable) > E(BigInt(0))

    SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause) match {
      case SatWithModel(model) =>
        symbols.valuateWithModel(model)(vd) match {
          case ADT(ADTType(`consID`, Seq(IntegerType)), _) =>
            // success!!
          case r =>
            fail("Unexpected valuation: " + r)
        }

      case r =>
        fail("Unexpected response: " + r)
    }
  }

  test("size(x) == 0 is satisfiable") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val tp = TypeParameter.fresh("A")
    val vd: ValDef = "x" :: T(listID)(tp)
    val clause = sizeFd(tp)(vd.toVariable) === E(BigInt(0))

    SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause) match {
      case SatWithModel(model) =>
        symbols.valuateWithModel(model)(vd) match {
          case ADT(ADTType(`nilID`, Seq(`tp`)), Seq()) =>
            // success!!
          case r =>
            fail("Unexpected valuation: " + r)
        }

      case r =>
        fail("Unexpected response: " + r)
    }
  }

  test("size(x) < 0 is not satisfiable (unknown)", ctx => {
    if (ctx.options.findOptionOrDefault(optSelectedSolvers) contains "princess") Ignore
    else Test
  }) { ctx =>
    val program = InoxProgram(ctx, symbols)

    val vd: ValDef = "x" :: T(listID)(IntegerType)
    val clause = sizeFd(IntegerType)(vd.toVariable) < E(BigInt(0))

    assert(!SimpleSolverAPI(SolverFactory.default(program).withTimeout(100)).solveSAT(clause).isSAT)
  }

  test("size(x) > size(y) is satisfiable") { ctx =>
    val program = InoxProgram(ctx, symbols)

    val x: ValDef = "x" :: T(listID)(IntegerType)
    val y: ValDef = "y" :: T(listID)(IntegerType)
    val clause = sizeFd(IntegerType)(x.toVariable) > sizeFd(IntegerType)(y.toVariable)

    assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause).isSAT)
  }

}
