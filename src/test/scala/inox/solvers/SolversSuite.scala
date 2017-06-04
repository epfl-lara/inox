/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import org.scalatest._

class SolversSuite extends FunSuite {
  import inox.trees._
  import SolverResponses._

  implicit val ctx = TestContext.empty.copy(options = Options(Seq(
    optCheckModels(true)
  )))

  val p = InoxProgram(ctx, NoSymbols)

  import p._
  import p.symbols._

  val solverNames: Seq[String] = {
    (if (SolverFactory.hasNativeZ3) Seq("nativez3") else Nil) ++
    (if (SolverFactory.hasZ3)       Seq("smt-z3") else Nil) ++
    (if (SolverFactory.hasCVC4)     Seq("smt-cvc4") else Nil)
  }

  val types = Seq(
    BooleanType,
    UnitType,
    CharType,
    RealType,
    IntegerType,
    Int8Type,
    BVType(13),
    Int16Type,
    Int32Type,
    BVType(33),
    Int64Type,
    StringType,
    TypeParameter.fresh("T"),
    SetType(IntegerType),
    BagType(IntegerType),
    MapType(IntegerType, IntegerType),
    FunctionType(Seq(IntegerType), IntegerType),
    TupleType(Seq(IntegerType, BooleanType, Int32Type))
  )

  val vs = types.map(tpe => Variable.fresh("v", tpe, true))

  // We need to make sure models are not co-finite
  val cnstrs = vs.map(v => v.getType match {
    case UnitType =>
      Equals(v, simplestValue(v.getType))
    case SetType(base) =>
      Not(ElementOfSet(simplestValue(base), v))
    case BagType(base) =>
      Not(Equals(MultiplicityInBag(simplestValue(base), v), simplestValue(IntegerType)))
    case MapType(from, to) =>
      Not(Equals(MapApply(v, simplestValue(from)), simplestValue(to)))
    case FunctionType(froms, to) =>
      Not(Equals(Application(v, froms.map(simplestValue(_))), simplestValue(to)))
    case _ =>
      not(Equals(v, simplestValue(v.getType)))
  })

  def checkSolver(sf: SolverFactory { val program: p.type }, vs: Set[Variable], cnstr: Expr): Unit = {
    SimpleSolverAPI(sf).solveSAT(cnstr) match {
      case SatWithModel(model) =>
        for (v <- vs) model.vars.get(v.toVal) match {
          case Some(e) =>
            assert(e.getType === v.tpe, s"Solver ${sf.name} - Extracting value of type ${v.tpe}")
          case _ =>
            fail(s"Solver ${sf.name} - Model does not contain ${v.id.uniqueName} of type ${v.tpe}")
        }
      case res =>
        fail(s"Solver ${sf.name} - Constraint ${cnstr.asString} is unsat!?")
    }
  }

  // Check that we correctly extract several types from solver models
  for (sname <- solverNames) {
    test(s"Model Extraction in $sname") {
      val sf = SolverFactory(sname, p, ctx.options)
      checkSolver(sf, vs.toSet, andJoin(cnstrs))
    }
  }
}
