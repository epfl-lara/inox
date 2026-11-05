/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Checks that every solver extracts non-trivial set, bag and map values from its models:
  * several elements, defaults, nested collections and functions that return collections.
  */
class CollectionModelSuite extends SolverTestSuite {
  override protected def options = Seq(optCheckModels(true))

  import inox.trees.{given, _}
  import SolverResponses._

  given Symbols = symbols

  private def int(i: Int): Expr = IntegerLiteral(i)
  private def set(tpe: Type, elems: Expr*): Expr = FiniteSet(elems, tpe)

  /** Checks that the solver finds values for `vars` that satisfy `constraint`. */
  private def checkModel(ctx: Context, vars: Seq[Variable], constraint: Expr): Unit = {
    solver(ctx).solveSAT(constraint) match {
      case SatWithModel(model) =>
        for (v <- vars) {
          val value = model.vars.getOrElse(v.toVal, fail(s"No value for $v in $model"))
          assert(value.getType == v.getType, s"Value $value of $v has type ${value.getType}")
          if (!v.getType.isInstanceOf[FunctionType])
            assert(symbols.isValue(value), s"Value $value of $v is not a value")
        }
        val evaluator = evaluators.RecursiveEvaluator(program, ctx)
        val res = evaluator.eval(exprOps.replaceFromSymbols(model.vars.map { case (vd, e) => vd.toVariable -> e }, constraint))
        assert(res.result == Some(BooleanLiteral(true)), s"Model $model doesn't satisfy $constraint ($res)")
      case res =>
        fail(s"Constraint $constraint is $res")
    }
  }

  private def modelTest(name: String, features: Feature*)(vars: Variable*)(constraint: Expr): Unit =
    test(name, features*)(ctx => checkModel(ctx, vars, constraint))

  locally {
    val v = Variable.fresh("v", SetType(IntegerType()))
    modelTest("Set with several elements", Sets, Integers)(v)(And(Seq(
      ElementOfSet(int(1), v), ElementOfSet(int(2), v), ElementOfSet(int(-4), v), Not(ElementOfSet(int(3), v))
    )))
  }

  locally {
    val v = Variable.fresh("v", SetType(Int32Type()))
    val w = Variable.fresh("w", SetType(Int32Type()))
    modelTest("Sets built from other sets", Sets)(v, w)(And(Seq(
      Equals(v, SetUnion(w, set(Int32Type(), Int32Literal(1)))),
      ElementOfSet(Int32Literal(2), w),
      Not(ElementOfSet(Int32Literal(3), v)),
      Not(Equals(SetIntersection(v, w), v))
    )))
  }

  locally {
    val v = Variable.fresh("v", SetType(TupleType(Seq(IntegerType(), BooleanType()))))
    modelTest("Set of tuples", Sets, Integers, ADTs)(v)(And(Seq(
      ElementOfSet(Tuple(Seq(int(1), BooleanLiteral(true))), v),
      ElementOfSet(Tuple(Seq(int(2), BooleanLiteral(false))), v),
      Not(ElementOfSet(Tuple(Seq(int(1), BooleanLiteral(false))), v))
    )))
  }

  locally {
    val v = Variable.fresh("v", SetType(StringType()))
    modelTest("Set of strings", Sets, Strings)(v)(And(Seq(
      ElementOfSet(StringLiteral("a"), v),
      ElementOfSet(StringLiteral("bc"), v),
      Not(ElementOfSet(StringLiteral(""), v))
    )))
  }

  locally {
    val v = Variable.fresh("v", SetType(SetType(IntegerType())))
    modelTest("Set of sets", Sets, Integers, NestedArrays)(v)(And(Seq(
      ElementOfSet(set(IntegerType(), int(1)), v),
      ElementOfSet(set(IntegerType()), v),
      Not(ElementOfSet(set(IntegerType(), int(2)), v))
    )))
  }

  locally {
    val v = Variable.fresh("v", BagType(IntegerType()))
    modelTest("Bag with several multiplicities", Bags, Integers)(v)(And(Seq(
      Equals(MultiplicityInBag(int(1), v), int(2)),
      Equals(MultiplicityInBag(int(2), v), int(3)),
      Equals(MultiplicityInBag(int(5), v), int(1)),
      Equals(MultiplicityInBag(int(3), v), int(0))
    )))
  }

  locally {
    val v = Variable.fresh("v", BagType(TupleType(Seq(IntegerType(), IntegerType()))))
    modelTest("Bag of tuples", Bags, Integers, ADTs)(v)(And(Seq(
      Equals(MultiplicityInBag(Tuple(Seq(int(1), int(2))), v), int(2)),
      Equals(MultiplicityInBag(Tuple(Seq(int(2), int(1))), v), int(1))
    )))
  }

  locally {
    val v = Variable.fresh("v", MapType(IntegerType(), IntegerType()))
    modelTest("Map with several keys", Maps, Integers)(v)(And(Seq(
      Equals(MapApply(v, int(1)), int(2)),
      Equals(MapApply(v, int(2)), int(3)),
      Equals(MapApply(v, int(7)), int(-1)),
      Equals(MapApply(v, int(10)), Plus(MapApply(v, int(11)), int(1)))
    )))
  }

  locally {
    val v = Variable.fresh("v", MapType(Int32Type(), BooleanType()))
    val w = Variable.fresh("w", MapType(Int32Type(), BooleanType()))
    modelTest("Maps built from other maps", Maps)(v, w)(And(Seq(
      Equals(v, MapUpdated(w, Int32Literal(1), BooleanLiteral(true))),
      Not(MapApply(w, Int32Literal(1))),
      MapApply(w, Int32Literal(2)),
      Not(MapApply(v, Int32Literal(3)))
    )))
  }

  locally {
    val v = Variable.fresh("v", MapType(IntegerType(), TupleType(Seq(IntegerType(), BooleanType()))))
    modelTest("Map to tuples", Maps, Integers, ADTs)(v)(And(Seq(
      Equals(MapApply(v, int(1)), Tuple(Seq(int(5), BooleanLiteral(true)))),
      Equals(MapApply(v, int(2)), Tuple(Seq(int(6), BooleanLiteral(false))))
    )))
  }

  locally {
    val v = Variable.fresh("v", MapType(IntegerType(), SetType(IntegerType())))
    modelTest("Map to sets", Maps, Sets, Integers, NestedArrays)(v)(And(Seq(
      ElementOfSet(int(1), MapApply(v, int(1))),
      ElementOfSet(int(2), MapApply(v, int(1))),
      Not(ElementOfSet(int(1), MapApply(v, int(2)))),
      ElementOfSet(int(3), MapApply(v, int(2)))
    )))
  }

  locally {
    val v = Variable.fresh("v", MapType(IntegerType(), MapType(IntegerType(), IntegerType())))
    modelTest("Map to maps", Maps, Integers, NestedArrays)(v)(And(Seq(
      Equals(MapApply(MapApply(v, int(1)), int(2)), int(3)),
      Equals(MapApply(MapApply(v, int(2)), int(2)), int(4))
    )))
  }

  locally {
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), SetType(IntegerType())))
    modelTest("Function returning sets", Functions, Sets, Integers)(f)(And(
      ElementOfSet(int(1), Application(f, Seq(int(1)))),
      Not(ElementOfSet(int(1), Application(f, Seq(int(2)))))
    ))
  }

  locally {
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), MapType(IntegerType(), IntegerType())))
    modelTest("Function returning maps", Functions, Maps, Integers)(f)(And(
      Equals(MapApply(Application(f, Seq(int(1))), int(1)), int(2)),
      Equals(MapApply(Application(f, Seq(int(2))), int(1)), int(3))
    ))
  }

  locally {
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), BagType(IntegerType())))
    modelTest("Function returning bags", Functions, Bags, Integers)(f)(And(
      Equals(MultiplicityInBag(int(1), Application(f, Seq(int(1)))), int(2)),
      Equals(MultiplicityInBag(int(1), Application(f, Seq(int(2)))), int(0))
    ))
  }
}
