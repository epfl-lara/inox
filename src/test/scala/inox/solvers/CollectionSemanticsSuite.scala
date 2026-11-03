/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** Set, bag and map operations on every solver. */
class CollectionSemanticsSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  given Symbols = symbols

  test("Set Operations", Sets) { ctx =>
    val s = solver(ctx)

    check(s, Equals(
      FiniteSet(Seq.empty, Int32Type()),
      FiniteSet(Seq.empty, Int32Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      FiniteSet(Seq(Int32Literal(9)), Int32Type()),
      FiniteSet(Seq.empty, Int32Type())
    ), BooleanLiteral(false))

    check(s, Equals(
      FiniteSet(Seq(Int8Literal(1), Int8Literal(2)), Int8Type()),
      FiniteSet(Seq(Int8Literal(2), Int8Literal(1)), Int8Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
      FiniteSet(Seq(Int32Literal(2), Int32Literal(1)), Int32Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2), Int32Literal(1)), Int32Type())
    ), BooleanLiteral(true))

    check(s, ElementOfSet(
      Int32Literal(1),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type())
    ), BooleanLiteral(true))

    check(s, ElementOfSet(
      Int32Literal(2),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type())
    ), BooleanLiteral(true))

    check(s, ElementOfSet(
      Int32Literal(3),
      FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type())
    ), BooleanLiteral(false))

    check(s, ElementOfSet(
      Int32Literal(3),
      SetAdd(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()), Int32Literal(3))
    ), BooleanLiteral(true))

    val v = Variable.fresh("v", Int32Type())

    assert(s.solveVALID(let(
      "s" :: SetType(Int32Type()),
      SetUnion(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()), FiniteSet(Seq(Int32Literal(1)), Int32Type()))
    )(s => And(
      ElementOfSet(Int32Literal(1), s),
      ElementOfSet(Int32Literal(2), s)
    ))) contains true)

    assert(s.solveVALID(let(
      "s" :: SetType(Int32Type()),
      SetUnion(FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()), FiniteSet(Seq(Int32Literal(1)), Int32Type()))
    )(s => or(Equals(v, Int32Literal(1)), Equals(v, Int32Literal(2)), Not(ElementOfSet(v, s))))) contains true)

    assert(s.solveVALID(or(
      Equals(v, Int32Literal(2)), Not(ElementOfSet(v, SetDifference(
        FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
        FiniteSet(Seq(Int32Literal(1)), Int32Type())
      )))
    )) contains true)

    assert(s.solveVALID(or(
      Equals(v, Int32Literal(2)), Not(ElementOfSet(v, SetDifference(
        FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
        FiniteSet(Seq.empty, Int32Type())
      )))
    )) contains false)

    assert(s.solveVALID(or(
      Equals(v, Int32Literal(2)), Not(ElementOfSet(v, SetIntersection(
        FiniteSet(Seq(Int32Literal(1), Int32Literal(2)), Int32Type()),
        FiniteSet(Seq(Int32Literal(2)), Int32Type())
      )))
    )) contains true)
  }

  test("Simple Bag Operations", Bags) { ctx =>
    val s = solver(ctx)

    assert(s.solveVALID(Equals(
      FiniteBag(Seq.empty, Int32Type()),
      FiniteBag(Seq.empty, Int32Type())
    )) contains true)

    assert(s.solveVALID(Equals(
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(1), Int32Literal(2) -> IntegerLiteral(2)), Int32Type()),
      FiniteBag(Seq(Int32Literal(2) -> IntegerLiteral(2), Int32Literal(1) -> IntegerLiteral(1)), Int32Type())
    )) contains true)

    assert(s.solveVALID(Equals(
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(1)), Int32Type()),
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(2), Int32Literal(1) -> IntegerLiteral(1)), Int32Type())
    )) contains true)

    check(s, MultiplicityInBag(
      Int32Literal(1),
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(2)), Int32Type())
    ), IntegerLiteral(2))
  }

  test("Bag Operations", Bags, BagAlgebra) { ctx =>
    val s = solver(ctx)

    check(s, Equals(
      FiniteBag(Seq(Int32Literal(9) -> IntegerLiteral(1)), Int32Type()),
      FiniteBag(Seq.empty, Int32Type())
    ), BooleanLiteral(false))

    check(s, MultiplicityInBag(
      Int32Literal(2),
      FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(2)), Int32Type())
    ), IntegerLiteral(0))

    check(s, MultiplicityInBag(
      Int32Literal(1),
      BagAdd(FiniteBag(Seq(Int32Literal(1) -> IntegerLiteral(1)), Int32Type()), Int32Literal(1))
    ), IntegerLiteral(2))

    check(s, Equals(
      BagUnion(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type()),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(1),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type())
      ),
      FiniteBag(Seq(
        Int32Literal(1) -> IntegerLiteral(1),
        Int32Literal(2) -> IntegerLiteral(3),
        Int32Literal(3) -> IntegerLiteral(1)
      ), Int32Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      BagUnion(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type()),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(2),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type())
      ),
      FiniteBag(Seq(
        Int32Literal(1) -> IntegerLiteral(1),
        Int32Literal(2) -> IntegerLiteral(3),
        Int32Literal(3) -> IntegerLiteral(1)
      ), Int32Type())
    ), BooleanLiteral(false))

    check(s, Equals(
      BagDifference(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type()),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(3),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type())
      ),
      FiniteBag(Seq(
        Int32Literal(1) -> IntegerLiteral(1)
      ), Int32Type())
    ), BooleanLiteral(true))

    check(s, Equals(
      BagIntersection(
        FiniteBag(Seq(
          Int32Literal(1) -> IntegerLiteral(1),
          Int32Literal(2) -> IntegerLiteral(2)
        ), Int32Type()),
        FiniteBag(Seq(
          Int32Literal(2) -> IntegerLiteral(3),
          Int32Literal(3) -> IntegerLiteral(1)
        ), Int32Type())
      ),
      FiniteBag(Seq(
        Int32Literal(2) -> IntegerLiteral(2)
      ), Int32Type())
    ), BooleanLiteral(true))
  }

  test("Bag Operations with repeated keys", Bags) { ctx =>
    val s = solver(ctx)

    val empty = FiniteBag(Seq.empty, IntegerType())
    // the key 1 occurs twice in the underlying representation of `twice`
    val twice = BagAdd(BagAdd(empty, IntegerLiteral(1)), IntegerLiteral(1))
    val five = FiniteBag(Seq(IntegerLiteral(1) -> IntegerLiteral(5)), IntegerType())

    check(s, MultiplicityInBag(IntegerLiteral(1), BagDifference(twice, empty)), IntegerLiteral(2))
    check(s, MultiplicityInBag(IntegerLiteral(1), BagDifference(five, twice)), IntegerLiteral(3))
    check(s, MultiplicityInBag(IntegerLiteral(1), BagIntersection(twice, five)), IntegerLiteral(2))
    check(s, MultiplicityInBag(IntegerLiteral(1), BagIntersection(BagUnion(twice, twice), five)), IntegerLiteral(4))
    check(s, MultiplicityInBag(IntegerLiteral(1),
      FiniteBag(Seq(IntegerLiteral(1) -> IntegerLiteral(-1)), IntegerType())), IntegerLiteral(0))
  }

  test("Map Operations", Maps) { ctx =>
    val s = solver(ctx)

    check(s, Equals(
      FiniteMap(Seq.empty, Int32Literal(12), Int32Type(), Int32Type()),
      FiniteMap(Seq.empty, Int32Literal(12), Int32Type(), Int32Type())
    ), BooleanLiteral(true))

    val v = Variable.fresh("v", Int32Type())

    assert(s.solveVALID(Equals(
      MapApply(FiniteMap(Seq.empty, Int32Literal(9), Int32Type(), Int32Type()), v),
      MapApply(FiniteMap(Seq.empty, Int32Literal(12), Int32Type(), Int32Type()), v)
    )) contains false)

    assert(s.solveVALID(Equals(
      MapApply(FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type()), v),
      MapApply(FiniteMap(Seq(Int32Literal(2) -> Int32Literal(3), Int32Literal(1) -> Int32Literal(2)), Int32Literal(9), Int32Type(), Int32Type()), v)
    )) contains true)

    assert(s.solveVALID(Equals(
      MapApply(FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type()), v),
      MapApply(FiniteMap(Seq(Int32Literal(2) -> Int32Literal(3), Int32Literal(1) -> Int32Literal(2)), Int32Literal(9), Int32Type(), Int32Type()), v)
    )) contains true)

    assert(s.solveVALID(Equals(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(1) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type()),
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(3), Int32Literal(1) -> Int32Literal(2)), Int32Literal(9), Int32Type(), Int32Type())
    )) contains false)

    assert(s.solveVALID(Equals(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(1) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type()),
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(3)), Int32Literal(9), Int32Type(), Int32Type())
    )) contains true)

    check(s, MapApply(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type(), Int32Type()),
      Int32Literal(1)
    ), Int32Literal(2))

    check(s, MapApply(
      FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type(), Int32Type()),
      Int32Literal(3)
    ), Int32Literal(6))

    check(s, MapApply(
      MapUpdated(
        FiniteMap(Seq(Int32Literal(1) -> Int32Literal(2), Int32Literal(2) -> Int32Literal(4)), Int32Literal(6), Int32Type(), Int32Type()),
        Int32Literal(1), Int32Literal(3)),
      Int32Literal(1)
    ), Int32Literal(3))
  }

  test("Z3 Set Extraction", Maps, Sets, Integers, NestedArrays) { ctx =>
    val s = solver(ctx)

    // Singleton set inside of a map is translated to (lambda ((x Int)) (= x 0))
    check(s,
      FiniteMap(Seq(), FiniteSet(Seq(IntegerLiteral(0)), IntegerType()), IntegerType(), SetType(IntegerType())),
      FiniteMap(Seq(), FiniteSet(Seq(IntegerLiteral(0)), IntegerType()), IntegerType(), SetType(IntegerType()))
    )
  }
}
