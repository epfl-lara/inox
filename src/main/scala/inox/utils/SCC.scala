/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

import scala.collection.immutable.ListSet

/** Returns the list of strongly connected sets of vertices.
  * A set is said strongly connected is from any vertex we can reach another vertex transitively.
  *
  * Each component comes after the components it reaches. With an `ordering`, the vertices and their
  * successors are visited in that order, so the components, and the vertices of each, come in an
  * order that depends only on the graph and the ordering, rather than on the hashes of the vertices.
  */
object SCC {
  def scc[T](graph: Map[T,Set[T]], ordering: Option[Ordering[T]] = None) : List[Set[T]] = {
    def inOrder(vs: Set[T]): Iterable[T] = ordering.fold(vs)(ord => vs.toSeq.sorted(using ord))

    // The first part is a shameless adaptation from Wikipedia
    val allVertices : Set[T] = graph.keySet ++ graph.values.flatten

    var index = 0
    var indices  : Map[T,Int] = Map.empty
    var lowLinks : Map[T,Int] = Map.empty
    var components : List[Set[T]] = Nil
    var s : List[T] = Nil

    def strongConnect(v: T): Unit = {
      indices  = indices.updated(v, index)
      lowLinks = lowLinks.updated(v, index)
      index += 1
      s = v :: s

      for (w <- inOrder(graph.getOrElse(v, Set.empty))) {
        if (!indices.isDefinedAt(w)) {
          strongConnect(w)
          lowLinks = lowLinks.updated(v, lowLinks(v) min lowLinks(w))
        } else if (s.contains(w)) {
          lowLinks = lowLinks.updated(v, lowLinks(v) min indices(w))
        }
      }

      if (lowLinks(v) == indices(v)) {
        var c : Set[T] = if (ordering.isDefined) ListSet.empty else Set.empty
        // do-while, Scala 3 style
        // See https://docs.scala-lang.org/scala3/reference/dropped-features/do-while.html
        while ({
          val x :: xs = s: @unchecked
          c = c + x
          s = xs
          // The line below is the do-while condition
          x != v
        }) () // This trailing () is important! If we remove it, it messes with the next statement

        components = c :: components
      }
    }

    for (v <- inOrder(allVertices)) {
      if (!indices.isDefinedAt(v)) {
        strongConnect(v)
      }
    }

    components.reverse
  }
}
