/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Calls on ground arguments, which the unrolling evaluates instead of unfolding them. A call that
  * the evaluator can't evaluate must still be unfolded, rather than taken to never return. */
class GroundCallSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  // def ext(x: BigInt): Boolean, which the evaluator can't call
  val extID = FreshIdentifier("ext")
  val extX = "x" :: IntegerType()
  val extFd = new FunDef(extID, Seq(), Seq(extX), BooleanType(),
    exprOps.uninterpretedCall("u", Seq(), Seq(extX), BooleanType()), Seq())

  // case class P(x: BigInt) { require(ext(x)) }
  val pID = FreshIdentifier("P")
  val pConsID = FreshIdentifier("P")
  val pX = FreshIdentifier("x")
  val pInvID = FreshIdentifier("pInv")
  val pInv = mkFunDef(pInvID)() { _ => (
    Seq("p" :: T(pID)()), BooleanType(), { case Seq(p) => E(extID)(p.getField(pX)) })
  }
  val pSort = mkSort(pID, HasADTInvariant(pInvID))() { _ => Seq((pConsID, Seq(ValDef(pX, IntegerType())))) }

  // def get(p: P): BigInt = p.x
  val getID = FreshIdentifier("get")
  val getFd = mkFunDef(getID)() { _ => (Seq("p" :: T(pID)()), IntegerType(), { case Seq(p) => p.getField(pX) }) }

  // def f(x: BigInt): BigInt, which is uninterpreted
  val fID = FreshIdentifier("f")
  val fX = "x" :: IntegerType()
  val fFd = new FunDef(fID, Seq(), Seq(fX), IntegerType(),
    UninterpretedCall(FreshIdentifier("f"), Seq(), Seq(fX.toVariable), FunctionType(Seq(IntegerType()), IntegerType())), Seq())

  override protected def symbols: Symbols =
    NoSymbols.withFunctions(Seq(extFd, pInv, getFd, fFd)).withSorts(Seq(pSort))
  given Symbols = symbols

  test("a ground call whose argument the evaluator can't build is unfolded", ADTs, Integers) { ctx =>
    // ext(0) && get(P(0)) != 42 holds of any model where ext(0) is true
    val query = E(extID)(E(BigInt(0))) && Not(E(getID)(ADT(pConsID, Seq(), Seq(E(BigInt(0))))) === E(BigInt(42)))
    val res = solver(ctx).solveSAT(query)
    assert(!res.isUNSAT, s"expected SAT or unknown, got $res")
  }

  test("a ground call is still evaluated", ADTs, Integers) { ctx =>
    val query = E(extID)(E(BigInt(0))) && Not(E(getID)(ADT(pConsID, Seq(), Seq(E(BigInt(0))))) === E(BigInt(0)))
    assert(solver(ctx).solveSAT(query).isUNSAT)
  }

  test("Uninterpreted calls are functions of their arguments", Integers) { ctx =>
    // def f(x: BigInt): BigInt, which has no body
    val s = solver(ctx)
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    def f(e: Expr) = FunctionInvocation(fID, Seq(), Seq(e))

    assert(s.solveVALID(Implies(Equals(x, y), Equals(f(x), f(y)))) contains true)
    assert(s.solveVALID(Equals(f(x), x)) contains false)
    assert(s.solveVALID(Equals(f(IntegerLiteral(1)), f(IntegerLiteral(2)))) contains false)
    s.solveSAT(And(Equals(f(x), IntegerLiteral(5)), Equals(f(y), IntegerLiteral(7)))) match {
      case SatWithModel(model) => assert(model.vars(x.toVal) != model.vars(y.toVal))
      case got => fail(s"Expected a model, got $got.")
    }
  }
}
