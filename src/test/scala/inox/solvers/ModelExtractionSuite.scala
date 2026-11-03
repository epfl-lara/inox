/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Checks that every solver can extract a model value of each type. */
class ModelExtractionSuite extends SolverTestSuite {
  override protected def options = Seq(optCheckModels(true))

  import inox.trees.{given, _}
  import SolverResponses._

  import program.{given, _}
  import program.symbols.{given, _}

  val types: Seq[(Type, Seq[Feature])] = Seq(
    BooleanType() -> Seq(),
    UnitType() -> Seq(),
    CharType() -> Seq(),
    Int8Type() -> Seq(),
    BVType(true, 13) -> Seq(),
    Int16Type() -> Seq(),
    Int32Type() -> Seq(),
    BVType(true, 33) -> Seq(),
    Int64Type() -> Seq(),
    BVType(false, 32) -> Seq(),
    IntegerType() -> Seq(Integers),
    RealType() -> Seq(Reals),
    StringType() -> Seq(Strings),
    TypeParameter.fresh("T") -> Seq(TypeParameters),
    SetType(IntegerType()) -> Seq(Sets, Integers),
    BagType(IntegerType()) -> Seq(Bags, Integers),
    MapType(IntegerType(), IntegerType()) -> Seq(Maps, Integers),
    FunctionType(Seq(IntegerType()), IntegerType()) -> Seq(Functions, Integers),
    TupleType(Seq(IntegerType(), BooleanType(), Int32Type())) -> Seq(ADTs, Integers),
  )

  // Models must not be trivial (in particular, not co-finite)
  def nonTrivial(v: Variable)(using Context): Expr = v.getType match {
    case UnitType() =>
      Equals(v, simplestValue(v.getType))
    case SetType(base) =>
      Not(ElementOfSet(simplestValue(base), v))
    case BagType(base) =>
      Not(Equals(MultiplicityInBag(simplestValue(base), v), simplestValue(IntegerType())))
    case MapType(from, to) =>
      Not(Equals(MapApply(v, simplestValue(from)), simplestValue(to)))
    case FunctionType(froms, to) =>
      Not(Equals(Application(v, froms.map(simplestValue(_))), simplestValue(to)))
    case _ =>
      Not(Equals(v, simplestValue(v.getType)))
  }

  for ((tpe, features) <- types) {
    test(s"Model extraction of ${tpe.asString}", features*) { ctx =>
      given Context = ctx
      val v = Variable.fresh("v", tpe, true)
      solver(ctx).solveSAT(nonTrivial(v)) match {
        case SatWithModel(model) => model.vars.get(v.toVal) match {
          case Some(e) => assert(e.getType == tpe, s"Extracted ${e.asString} for type ${tpe.asString}")
          case None => fail(s"Model doesn't contain a value for ${tpe.asString}")
        }
        case res => fail(s"Constraint ${nonTrivial(v).asString} is $res")
      }
    }
  }
}
