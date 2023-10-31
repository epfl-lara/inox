/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

import scala.Iterable
object Graphs {
  trait EdgeLike[Node] {
    val _1: Node
    val _2: Node
  }

  case class SimpleEdge[Node](_1: Node, _2: Node) extends EdgeLike[Node]
  case class LabeledEdge[Label, Node](_1: Node, _2: Node, l: Label) extends EdgeLike[Node]

  trait DiGraphLike[Node, Edge <: EdgeLike[Node], G <: DiGraphLike[Node, Edge, G]] {
    // The vertices
    def N: Set[Node]
    // The edges
    def E: Set[Edge]

    // Returns the set of incoming edges for a given vertex
    def inEdges(n: Node)  = E.filter(_._2 == n)
    // Returns the set of outgoing edges for a given vertex
    def outEdges(n: Node)  = E.filter(_._1 == n)

    // Returns the set of edges between two vertices
    def edgesBetween(from: Node, to: Node) = {
      E.filter(e => e._1 == from && e._2 == to)
    }

    // Adds a new vertex
    def + (n: Node): G
    // Adds new vertices
    def ++ (ns: Iterable[Node]): G
    // Adds a new edge
    def + (e: Edge): G
    // Removes a vertex from the graph
    def - (from: Node): G
    // Removes a number of vertices from the graph
    def -- (from: Iterable[Node]): G
    // Removes an edge from the graph
    def - (from: Edge): G
  }

  // Implementation note: inEdgesMap and outEdgesMap can be derived from N and E.
  // However, since `inEdges` and `outEdges` are often used with updated copies of the graph,
  // it is interesting performance-wise to have these maps as fields and "update"
  // them alongside "update" operation such as +, ++ etc.
  case class DiGraph[Node, Edge <: EdgeLike[Node]] private(N: Set[Node], E: Set[Edge], inEdgesMap: Map[Node, Set[Edge]], outEdgesMap: Map[Node, Set[Edge]])
    extends DiGraphLike[Node, Edge, DiGraph[Node, Edge]]
       with DiGraphOps[Node, Edge, DiGraph[Node, Edge]]{

    override def inEdges(n: Node): Set[Edge] = inEdgesMap.getOrElse(n, Set.empty)
    override def outEdges(n: Node): Set[Edge] = outEdgesMap.getOrElse(n, Set.empty)

    def +(n: Node) = {
      // If n is already present, do not override the set of edges in the edges map
      val newInEdgesMap = inEdgesMap.updatedWith(n)(_.orElse(Some(Set.empty)))
      val newOutEdgesMap = outEdgesMap.updatedWith(n)(_.orElse(Some(Set.empty)))
      DiGraph(N + n, E, newInEdgesMap, newOutEdgesMap)
    }
    def ++(ns: Iterable[Node]) = {
      def addIfPresent(map: Map[Node, Set[Edge]]): Map[Node, Set[Edge]] =
        ns.foldLeft(map) { case (map, n) => map.updatedWith(n)(_.orElse(Some(Set.empty))) }

      val newInEdgesMap = addIfPresent(inEdgesMap)
      val newOutEdgesMap = addIfPresent(outEdgesMap)
      DiGraph(N ++ ns, E, newInEdgesMap, newOutEdgesMap)
    }
    def +(e: Edge) = {
      val newInEdgesMap = inEdgesMap.updatedWith(e._2)(_.map(_ + e).orElse(Some(Set(e))))
      val newOutEdgesMap = outEdgesMap.updatedWith(e._1)(_.map(_ + e).orElse(Some(Set(e))))
      DiGraph(N + e._1 + e._2, E + e, newInEdgesMap, newOutEdgesMap)
    }

    def -(n: Node) = DiGraph(N - n, E.filter(e => e._1 == n || e._2 == n), inEdgesMap - n, outEdgesMap - n)
    def --(ns: Iterable[Node]) = {
      val toRemove = ns.toSet
      DiGraph(N -- toRemove, E.filterNot(e => toRemove.contains(e._1) || toRemove.contains(e._2)), inEdgesMap -- toRemove, outEdgesMap -- toRemove)
    }
    def -(e: Edge) = {
      val newInEdgesMap = inEdgesMap.updatedWith(e._2)(_.map(_ - e))
      val newOutEdgesMap = outEdgesMap.updatedWith(e._1)(_.map(_ - e))
      DiGraph(N, E - e, newInEdgesMap, newOutEdgesMap)
    }
  }
  object DiGraph {
    def apply[Node, Edge <: EdgeLike[Node]](N: Set[Node] = Set.empty[Node], E: Set[Edge] = Set.empty[Edge]): DiGraph[Node, Edge] = {
      val inEdgesMap = N.map(n => n -> E.filter(_._2 == n)).toMap
      val outEdgesMap = N.map(n => n -> E.filter(_._1 == n)).toMap
      DiGraph(N, E, inEdgesMap, outEdgesMap)
    }
  }

  trait DiGraphOps[Node, Edge <: EdgeLike[Node], G <: DiGraphLike[Node, Edge, G]] {
    this: G =>

    def sources: Set[Node] = {
      N -- E.map(_._2)
    }

    def sinks: Set[Node] = {
      N -- E.map(_._1)
    }

    def stronglyConnectedComponents: DiGraph[Set[Node], SimpleEdge[Set[Node]]] = {
      // Tarjan's algorithm
      var index = 0
      var stack = List[Node]()

      var indexes  = Map[Node, Int]()
      var lowlinks = Map[Node, Int]()
      var onStack  = Set[Node]()

      var nodesToScc = Map[Node, Set[Node]]()
      var res = DiGraph[Set[Node], SimpleEdge[Set[Node]]]()

      def strongConnect(n: Node): Unit = {
        indexes  += n -> index
        lowlinks += n -> index
        index += 1

        stack = n :: stack
        onStack += n

        for (m <- succ(n)) {
          if (!(indexes contains m)) {
            strongConnect(m)
            lowlinks += n -> (lowlinks(n) min lowlinks(m))
          } else if (onStack(m)) {
            lowlinks += n -> (lowlinks(n) min indexes(m))
          }
        }

        if (lowlinks(n) == indexes(n)) {
          val i = stack.indexOf(n)+1
          val ns = stack.take(i)
          stack = stack.drop(i)
          val scc = ns.toSet
          onStack --= ns
          nodesToScc ++= ns.map(n => n -> scc)
          res += scc
        }
      }


      for (n <- N if !(indexes contains n)) {
        strongConnect(n)
      }

      for (e <- E) {
        val s1 = nodesToScc(e._1)
        val s2 = nodesToScc(e._2)
        if (s1 != s2) {
          res += SimpleEdge(s1, s2)
        }
      }

      res
    }

    def topSort: Seq[Node] = {
      var res = List[Node]()

      var temp = Set[Node]()
      var perm = Set[Node]()

      def visit(n: Node): Unit = {
        if (temp(n)) {
          throw new IllegalArgumentException("Graph is not a DAG")
        } else if (!perm(n)) {
          temp += n
          for (n2 <- succ(n)) {
            visit(n2)
          }
          perm += n
          temp -= n
          res ::= n
        }
      }

      for (n <- N if !temp(n) && !perm(n)) {
        visit(n)
      }

      res
    }

    def depthFirstSearch(from: Node)(f: Node => Unit): Unit = {
      var visited = Set[Node]()

      var stack = List[Node]()

      stack ::= from

      while (stack.nonEmpty) {
        val (n :: rest) = stack: @unchecked
        stack = rest
        visited += n
        f(n)
        for (n2 <- succ(n) if !visited(n2)) {
          stack ::= n2
        }
      }
    }

    def fold[T](from: Node)(
      follow: Node => Iterable[Node],
      map: Node => T,
      compose: List[T] => T): T = {

      var visited = Set[Node]()

      def visit(n: Node): T = {
        visited += n

        val toFollow = follow(n).filterNot(visited)
        visited ++= toFollow

        compose(map(n) :: toFollow.toList.map(visit))
      }

      compose(follow(from).toList.map(visit))
    }

    def succ(from: Node): Set[Node] = {
      outEdges(from).map(_._2)
    }

    def pred(from: Node): Set[Node] = {
      inEdges(from).map(_._1)
    }

    def transitiveSucc(from: Node): Set[Node] = {
      fold[Set[Node]](from)(
        succ,
        Set(_),
        _.toSet.flatten
      )
    }

    def transitivePred(from: Node): Set[Node] = {
      fold[Set[Node]](from)(
        pred,
        Set(_),
        _.toSet.flatten
      )
    }

    def breadthFirstSearch(from: Node)(f: Node => Unit): Unit = {
      var visited = Set[Node]()

      val queue = new collection.mutable.Queue[Node]()

      queue += from

      while(queue.nonEmpty) {
        val n = queue.dequeue()
        visited += n
        f(n)
        for (n2 <- succ(n) if !visited(n2)) {
          queue += n2
        }
      }
    }
  }
}
