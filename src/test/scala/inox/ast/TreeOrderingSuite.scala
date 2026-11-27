/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

class TreeOrderingSuite extends AnyFunSuite {
  import inox.trees._

  val ordering = treeOrdering[Type]

  test("identifiers of the same name compare by their creation, whatever was created between them") {
    val a1 = FreshIdentifier("A")
    (1 to 100).foreach(_ => FreshIdentifier("other"))
    val a2 = FreshIdentifier("A")
    assert(ordering.compare(ADTType(a1, Seq()), ADTType(a2, Seq())) < 0)
    assert(ordering.compare(ADTType(a2, Seq()), ADTType(a1, Seq())) > 0)
  }

  test("types compare by their structure") {
    val a = FreshIdentifier("A")
    val t1 = TupleType(Seq(IntegerType(), ADTType(a, Seq(BooleanType()))))
    val t2 = TupleType(Seq(IntegerType(), ADTType(a, Seq(IntegerType()))))
    assert(ordering.compare(t1, t1.copy()) == 0)
    assert(ordering.compare(t1, t2) == -ordering.compare(t2, t1))
    assert(ordering.compare(t1, t2) != 0)
    assert(ordering.compare(TupleType(Seq(IntegerType(), IntegerType())), TupleType(Seq(IntegerType(), IntegerType(), IntegerType()))) < 0)
  }

  test("leaves compare by their other fields") {
    assert(ordering.compare(BVType(true, 8), BVType(true, 32)) != 0)
    assert(ordering.compare(BVType(true, 8), BVType(true, 8)) == 0)
    assert(ordering.compare(BVType(true, 8), BVType(false, 8)) != 0)
  }
}
