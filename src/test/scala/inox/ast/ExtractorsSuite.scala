/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

class ExtractorsSuite extends AnyFunSuite {
  import inox.trees._

  test("Extractors do not simplify basic arithmetic") {
    val e1 = Plus(Int32Literal(1), Int32Literal(1))
    val e2 = e1 match {
      case Operator(es, builder) => builder(es)
      case _ => fail(s"$e1 did not match Operator extractor")
    }
    assert(e1 === e2)

    val e3 = Times(Variable.fresh("x", IntegerType()), IntegerLiteral(1))
    val e4 = e3 match {
      case Operator(es, builder) => builder(es)
      case _ => fail(s"$e3 did not match Operator extractor")
    }
    assert(e3 === e4)

    val e5 = Plus(Int8Literal(1), Int8Literal(1))
    val e6 = e5 match {
      case Operator(es, builder) => builder(es)
      case _ => fail(s"$e5 did not match Operator extractor")
    }
    assert(e5 === e6)

    val size = 13
    val e7 = Plus(BVLiteral(true, 1, size), BVLiteral(true, 1, size))
    val e8 = e7 match {
      case Operator(es, builder) => builder(es)
      case _ => fail(s"$e7 did not match Operator extractor")
    }
    assert(e7 === e8)
  }

  test("Extractors do not magically change the syntax") {
    val e1 = Equals(IntegerLiteral(1), IntegerLiteral(1))
    val e2 = e1 match {
      case Operator(es, builder) => builder(es)
      case _ => fail(s"$e1 did not match Operator extractor")
    }
    assert(e1 === e2)

    val e3 = Equals(BooleanLiteral(true), BooleanLiteral(false))
    val e4 = e3 match {
      case Operator(es, builder) => builder(es)
      case _ => fail(s"$e3 did not match Operator extractor")
    }
    assert(e3 === e4)

    val e5 = TupleSelect(Tuple(Seq(IntegerLiteral(1), IntegerLiteral(2))), 2)
    val e6 = e5 match {
      case Operator(es, builder) => builder(es)
      case _ => fail(s"$e5 did not match Operator extractor")
    }
    assert(e5 === e6)
  }


  test("Extractors of map operations") {
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    val z = Variable.fresh("z", IntegerType())

    val a1 = FiniteMap(
      Seq(Int32Literal(0) -> x, Int32Literal(3) -> y, Int32Literal(5) -> z),
      IntegerLiteral(10),
      Int32Type(),
      IntegerType())
    val a2 = a1 match {
      case Operator(es, builder) =>
        assert(es === Seq(Int32Literal(0), x, Int32Literal(3), y, Int32Literal(5), z, IntegerLiteral(10)))
        builder(es)
      case _ => fail(s"$a1 did not match Operator extractor")
    }
    assert(a2 === a1)

    val app1 = MapApply(a1, Int32Literal(0))
    val app2 = app1 match {
      case Operator(es, builder) =>
        assert(es === Seq(a1, Int32Literal(0)))
        builder(es)
      case _ => fail(s"$app1 did not match Operator extractor")
    }
    assert(app1 === app2)
  }

}
