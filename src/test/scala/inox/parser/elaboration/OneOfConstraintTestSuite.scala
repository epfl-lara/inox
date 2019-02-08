package inox.parser.elaboration

import inox.ast.Trees
import inox.parser.Elaborators
import org.scalatest._

class OneOfConstraintTestSuite extends FunSuite with Elaborators
{

  override protected val trees: Trees = inox.trees

  test("Simple one of") {
    val first = SimpleTypes.Unknown.fresh
    val second = SimpleTypes.Unknown.fresh

    val constraints = Seq(Constraint.equal(second, SimpleTypes.IntegerType()),
      Constraint.oneOf(first, second, Seq(SimpleTypes.IntegerType(), SimpleTypes.BooleanType(), SimpleTypes.RealType())),
      Constraint.exist(first),
      Constraint.exist(second))

    val result = solve(constraints)

    result match {
      case Right(unifier) =>
        assert(unifier.get(first) == SimpleTypes.IntegerType(), "Simple OneOf constraint solved")
      case Left(errorMessage) => fail(errorMessage)
    }
  }


  test("Simple one of, not unifiable test") {
    val first = SimpleTypes.Unknown.fresh
    val second = SimpleTypes.Unknown.fresh

    val constraints = Seq(Constraint.equal(second, SimpleTypes.IntegerType()),
      Constraint.oneOf(first, second, Seq(SimpleTypes.BooleanType(), SimpleTypes.RealType())),
      Constraint.exist(first),
      Constraint.exist(second))

    val result = solve(constraints)

    result match {
      case Right(unifier) =>
        fail("Should not be able to unify")
      case Left(errorMessage) =>
        succeed
    }
  }

  test("One of depends on the result of another") {
    val first = SimpleTypes.Unknown.fresh
    val second = SimpleTypes.Unknown.fresh
    val third = SimpleTypes.Unknown.fresh

    val constraints = Seq(
      Constraint.oneOf(second, first, Seq(
        SimpleTypes.FunctionType(Seq(SimpleTypes.BitVectorType(true, 32)), first),
        SimpleTypes.RealType(),
        third
      )), Constraint.equal(first, SimpleTypes.BitVectorType(true, 32)),
      Constraint.exist(first), Constraint.exist(second), Constraint.exist(third))

    val result = solve(constraints)

    result match {
      case Right(unifier) =>
        assert(unifier.get(second) == SimpleTypes.BitVectorType(true, 32) && unifier.get(third) == SimpleTypes.BitVectorType(true, 32), "Simple OneOf constraint solved")
      case Left(errorMessage) => fail(errorMessage)
    }
  }

  test("Two one of, result of one solves the other") {
    val first = SimpleTypes.Unknown.fresh
    val second = SimpleTypes.Unknown.fresh
    val third = SimpleTypes.Unknown.fresh

    val constraints = Seq(
      Constraint.oneOf(second, third, Seq(
        SimpleTypes.FunctionType(Seq(SimpleTypes.BitVectorType(true, 32)), first),
        SimpleTypes.RealType(),
        SimpleTypes.BitVectorType(true, 32)
      )), Constraint.oneOf(third, first, Seq(
        SimpleTypes.MapType(SimpleTypes.IntegerType(), SimpleTypes.BooleanType()),
        SimpleTypes.BagType(SimpleTypes.StringType()),
        SimpleTypes.BitVectorType(true, 32)
      )), Constraint.equal(first, SimpleTypes.BitVectorType(true, 32)),
      Constraint.exist(first), Constraint.exist(second), Constraint.exist(third))

    val result = solve(constraints)

    result match {
      case Right(unifier) =>
        assert(unifier.get(second) == SimpleTypes.BitVectorType(true, 32) && unifier.get(third) == SimpleTypes.BitVectorType(true, 32), "Simple OneOf constraint solved")
      case Left(errorMessage) => fail(errorMessage)
    }
  }


  test("Function overloading constraints") {
    val first = SimpleTypes.Unknown.fresh
    val second = SimpleTypes.Unknown.fresh
    val third = SimpleTypes.Unknown.fresh
    val fourth = SimpleTypes.Unknown.fresh

    val constraints = Seq(
      Constraint.oneOf(first, first, Seq(
        SimpleTypes.FunctionType(Seq(
          SimpleTypes.BitVectorType(true, 32), SimpleTypes.BitVectorType(true, 32)), SimpleTypes.BooleanType()
        ),
        SimpleTypes.FunctionType(Seq(
          SimpleTypes.StringType(), SimpleTypes.StringType()), SimpleTypes.BooleanType())
        ))
      ,
      Constraint.equal(first, SimpleTypes.FunctionType(Seq(second, third), fourth)),
      Constraint.equal(second, SimpleTypes.StringType()),
      Constraint.equal(third, SimpleTypes.StringType()),
      Constraint.exist(first),
      Constraint.exist(second),
      Constraint.exist(third),
      Constraint.exist(fourth)
    )

    val result = solve(constraints)

    result match {
      case Right(unifier) =>
        assert(unifier.get(first) == SimpleTypes.FunctionType(Seq(SimpleTypes.StringType(), SimpleTypes.StringType()),
          SimpleTypes.BooleanType()))
        assert(unifier.get(second) == SimpleTypes.StringType())
        assert(unifier.get(third) == SimpleTypes.StringType())
        assert(unifier.get(fourth) == SimpleTypes.BooleanType())
      case Left(errorMessage) => fail(errorMessage)
    }
  }

  test("Function overloaded no parameter combination") {
    val first = SimpleTypes.Unknown.fresh
    val second = SimpleTypes.Unknown.fresh
    val third = SimpleTypes.Unknown.fresh
    val fourth = SimpleTypes.Unknown.fresh

    val constraints = Seq(
      Constraint.oneOf(first, first, Seq(
        SimpleTypes.FunctionType(Seq(
          SimpleTypes.BitVectorType(true, 32), SimpleTypes.BitVectorType(true, 32)), SimpleTypes.BooleanType()
        ),
        SimpleTypes.FunctionType(Seq(
          SimpleTypes.StringType(), SimpleTypes.StringType()), SimpleTypes.BooleanType())
      ))
      ,
      Constraint.equal(first, SimpleTypes.FunctionType(Seq(second, third), fourth)),
      Constraint.equal(second, SimpleTypes.StringType()),
      Constraint.equal(third, SimpleTypes.BitVectorType(true, 32)),
      Constraint.exist(first),
      Constraint.exist(second),
      Constraint.exist(third),
      Constraint.exist(fourth)
    )

    val result = solve(constraints)

    result match {
      case Right(unifier) =>
        fail("Should raise an exception no possible option")
      case Left(errorMessage) => succeed
    }
  }

  test("Function overloading, no overloaded has the necessary result type") {
    val first = SimpleTypes.Unknown.fresh
    val second = SimpleTypes.Unknown.fresh
    val third = SimpleTypes.Unknown.fresh
    val fourth = SimpleTypes.Unknown.fresh

    val constraints = Seq(
      Constraint.oneOf(first, first, Seq(
        SimpleTypes.FunctionType(Seq(
          SimpleTypes.BitVectorType(true, 32), SimpleTypes.BitVectorType(true, 32)), SimpleTypes.BooleanType()
        ),
        SimpleTypes.FunctionType(Seq(
          SimpleTypes.StringType(), SimpleTypes.StringType()), SimpleTypes.BooleanType())
      ))
      ,
      Constraint.equal(first, SimpleTypes.FunctionType(Seq(second, third), fourth)),
      Constraint.equal(second, SimpleTypes.StringType()),
      Constraint.equal(third, SimpleTypes.StringType()),
      Constraint.equal(fourth, SimpleTypes.CharType()),
      Constraint.exist(first),
      Constraint.exist(second),
      Constraint.exist(third),
      Constraint.exist(fourth)
    )

    val result = solve(constraints)

    result match {
      case Right(unifier) =>
        fail("Should raise an exception no possible option")
      case Left(errorMessage) => succeed
    }

  }
}
