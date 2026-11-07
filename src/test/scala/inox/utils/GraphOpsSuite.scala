/* Copyright 2009-2026 EPFL, Lausanne */

package inox.utils

import org.scalatest.funsuite.AnyFunSuite

class GraphOpsSuite extends AnyFunSuite {
  import GraphOps._

  test("topologicalSorting orders a DAG after the predecessors") {
    val preds = Map(1 -> Set.empty[Int], 2 -> Set(1), 3 -> Set(1, 2), 4 -> Set(3))
    val Right(order) = topologicalSorting(preds): @unchecked
    assert(order.toSet == preds.keySet)
    for ((n, ps) <- preds; p <- ps) assert(order.indexOf(p) < order.indexOf(n))
  }

  test("topologicalSorting returns the nodes on and after a cycle") {
    val preds = Map(1 -> Set.empty[Int], 2 -> Set(1, 3), 3 -> Set(2), 4 -> Set(3))
    assert(topologicalSorting(preds) == Left(Set(2, 3, 4)))
  }

  test("topologicalSorting accepts predecessors that aren't keys") {
    assert(topologicalSorting(Map(2 -> Set(1))) == Right(Seq(1, 2)))
  }

  test("transitiveClosure") {
    val graph = Map(1 -> Set(2), 2 -> Set(3), 3 -> Set(1), 4 -> Set(4), 5 -> Set.empty[Int])
    assert(transitiveClosure(graph) == Map(
      1 -> Set(1, 2, 3), 2 -> Set(1, 2, 3), 3 -> Set(1, 2, 3), 4 -> Set(4), 5 -> Set()))
  }

  test("sources and sinks") {
    val graph = Map(1 -> Set(2), 2 -> Set(3), 3 -> Set.empty[Int], 4 -> Set(2))
    assert(sources(graph) == Set(1, 4))
    assert(sinks(graph) == Set(3))
  }

  test("reachable excludes the source unless it is on a cycle") {
    val next = Map(1 -> Set(2), 2 -> Set(3), 3 -> Set(2), 4 -> Set(4)).withDefaultValue(Set.empty[Int])
    assert(reachable(next, 1) == Set(2, 3))
    assert(reachable(next, 2) == Set(2, 3))
    assert(reachable(next, 4) == Set(4))
    assert(reachable(next, 5) == Set())
  }

  test("isReachable") {
    val next = Map(1 -> Set(2), 2 -> Set(3), 3 -> Set(2)).withDefaultValue(Set.empty[Int])
    assert(isReachable(next, 1, 3))
    assert(isReachable(next, 2, 2))
    assert(!isReachable(next, 1, 1))
    assert(!isReachable(next, 3, 1))
  }
}
