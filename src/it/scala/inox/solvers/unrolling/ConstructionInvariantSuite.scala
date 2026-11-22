/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

import SolverResponses._

/** Constructing a value of a sort with an invariant fails when the value doesn't satisfy it, as in
  * the evaluator (see `SymbolOps.definedness`). */
class ConstructionInvariantSuite extends UnrollingTestSuite {
  import inox.trees._
  import dsl._

  override protected def optionMatrix = UnrollingTestSuite.combinations(
    Seq(optFunctionEquality(FunctionEquality.Extensional)),
    Seq(optCheckModels(true)),
  )

  // case class Pos(v: BigInt) { require(v > 0) }
  val posID = FreshIdentifier("Pos")
  val mkPosID = FreshIdentifier("MkPos")
  val vID = FreshIdentifier("v")
  val posInvID = FreshIdentifier("posInv")
  val posInv = mkFunDef(posInvID)() { _ => (
    Seq("p" :: T(posID)()), BooleanType(), { case Seq(p) => p.getField(vID) > E(BigInt(0)) })
  }
  val posSort = mkSort(posID, HasADTInvariant(posInvID))() { _ =>
    Seq((mkPosID, Seq(ValDef(vID, IntegerType()))))
  }

  val getVID = FreshIdentifier("getV")
  val getV = mkFunDef(getVID)() { _ => (Seq("p" :: T(posID)()), IntegerType(), { case Seq(p) => p.getField(vID) }) }

  val program = InoxProgram(new Symbols(Map(posInvID -> posInv, getVID -> getV), Map(posID -> posSort)))

  private def result(clause: Expr)(using Context) = SimpleSolverAPI(program.getSolver).solveSAT(clause)

  def mkPos(e: Expr): Expr = ADT(mkPosID, Seq(), Seq(e))

  test("a function that constructs a value breaking its invariant fails") { ctx ?=>
    val f = Variable.fresh("f", IntegerType() =>: IntegerType())
    val ident = \("y" :: IntegerType())(y => y)
    // `y => Pos(y).v` fails where `y <= 0`, so it differs from `y => y` under extensional equality
    for (lambda <- Seq(\("y" :: IntegerType())(y => mkPos(y).getField(vID)), \("y" :: IntegerType())(y => E(getVID)(mkPos(y))))) {
      assert(program.getEvaluator.eval(Equals(lambda, ident)).result == Some(BooleanLiteral(false)))
      result(f === lambda && !(f === ident)) match {
        case SatWithModel(_) =>
        case res => fail(s"Expected a model for $lambda, got $res")
      }
    }
  }

  test("a formula that constructs a value breaking its invariant fails") { ctx ?=>
    val x = Variable.fresh("x", IntegerType())
    assert(result(x === E(BigInt(0)) && mkPos(x).getField(vID) === E(BigInt(0))) == Unsat)
    assert(result(x === E(BigInt(0)) && E(getVID)(mkPos(x)) === E(BigInt(0))) == Unsat)
    assert(result(x === E(BigInt(1)) && mkPos(x).getField(vID) === E(BigInt(1))).isSAT)
  }
}
