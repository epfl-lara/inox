/* Copyright 2009-2026 EPFL, Lausanne */

package inox.utils

import org.scalatest.funsuite.AnyFunSuite

class SeqUtilsSuite extends AnyFunSuite {
  import SeqUtils._

  test("cartesianProduct") {
    assert(cartesianProduct(Seq(Seq(1, 2), Seq(3), Seq(4, 5))).toSet ==
      Set(Seq(1, 3, 4), Seq(2, 3, 4), Seq(1, 3, 5), Seq(2, 3, 5)))
    assert(cartesianProduct(Seq(Seq(1, 2), Seq())) == Seq())
    assert(cartesianProduct(Seq.empty[Seq[Int]]) == Seq(Seq()))
  }

  test("sumTo lists the compositions into positive parts") {
    assert(sumTo(4, 2).toSet == Set(Seq(1, 3), Seq(2, 2), Seq(3, 1)))
    assert(sumTo(3, 3) == Seq(Seq(1, 1, 1)))
    assert(sumTo(2, 3) == Seq())
    assert(sumTo(5, 1) == Seq(Seq(5)))
    for (s <- 1 to 6; a <- 1 to 4; c <- sumTo(s, a)) assert(c.size == a && c.sum == s && c.forall(_ > 0))
  }

  test("sumToOrdered lists the non-decreasing compositions into positive parts") {
    assert(sumToOrdered(4, 2).toSet == Set(Seq(1, 3), Seq(2, 2)))
    assert(sumToOrdered(6, 3).toSet == Set(Seq(1, 1, 4), Seq(1, 2, 3), Seq(2, 2, 2)))
    assert(sumToOrdered(2, 3) == Seq())
    for (s <- 1 to 8; a <- 1 to 4) {
      assert(sumToOrdered(s, a).toSet == sumTo(s, a).filter(c => c == c.sorted).toSet)
    }
  }

  test("groupWhile groups the runs of elements that satisfy the predicate") {
    assert(groupWhile(Seq(1, 3, 2, 4, 5, 7, 6))(_ % 2 == 1) == Seq(Seq(1, 3), Seq(2), Seq(4), Seq(5, 7), Seq(6)))
    assert(groupWhile(Seq.empty[Int])(_ => true) == Seq())
  }
}
