/* Copyright 2009-2026 EPFL, Lausanne */

package inox.utils

import org.scalatest.funsuite.AnyFunSuite

class IncrementalCollectionsSuite extends AnyFunSuite {

  test("IncrementalMap restores its bindings on pop") {
    val m = new IncrementalMap[Int, String]
    m += 1 -> "a"
    m.push()
    m += 1 -> "b"
    m += 2 -> "c"
    m -= 1
    assert(m.toMap == Map(2 -> "c"))
    m.pop()
    assert(m.toMap == Map(1 -> "a"))
    assert(m(1) == "a" && m.get(2).isEmpty && !m.contains(2))
    assert(m.getOrElse(2, "z") == "z")
    assert(m.cached(2)("d") == "d" && m.cached(2)("e") == "d")
    m.reset()
    assert(m.isEmpty)
  }

  test("IncrementalMap.withDefaultValue keeps the frames in order") {
    val m = new IncrementalMap[Int, Int]
    m += 1 -> 1
    m.push()
    m += 1 -> 2
    m.push()
    m += 1 -> 3

    val d = m.withDefaultValue(0)
    assert(d(1) == 3 && d(42) == 0)
    d.pop()
    assert(d(1) == 2 && d(42) == 0)
    d.pop()
    assert(d(1) == 1 && d(42) == 0)
  }

  test("IncrementalMap.withDefaultValue keeps its default across push, pop and clear") {
    val d = new IncrementalMap[Int, Set[Int]].withDefaultValue(Set.empty)
    assert(d(1) == Set.empty)
    d += 1 -> Set(1)
    d.push()
    assert(d(1) == Set(1) && d(2) == Set.empty)
    d += 2 -> Set(2)
    d.pop()
    assert(d(2) == Set.empty)
    d.clear()
    assert(d(1) == Set.empty)
  }

  test("IncrementalSet restores its elements on pop") {
    val s = new IncrementalSet[Int]
    s += 1
    s.push()
    s += 2
    s -= 1
    assert(s.toSet == Set(2) && s(2) && !s.contains(1))
    s.pop()
    assert(s.toSet == Set(1))
    s.clear()
    assert(s.isEmpty)
  }

  test("IncrementalSeq restores its elements on pop") {
    val s = new IncrementalSeq[Int]
    s += 1
    s += 2
    s.push()
    s += 3
    s -= 1
    assert(s.toList == List(2, 3))
    s.pop()
    assert(s.toList == List(1, 2))
    s.reset()
    assert(s.isEmpty)
  }
}
