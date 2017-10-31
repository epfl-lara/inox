/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import utils.Graphs._

trait CallGraph {
  protected val trees: Trees
  import trees._
  import trees.exprOps._
  protected val symbols: Symbols

  private def collectCalls(fd: FunDef)(e: Expr): Set[(Identifier, Identifier)] = e match {
    case f @ FunctionInvocation(id, tps, _) => Set((fd.id, id))
    case _ => Set()
  }

  private[this] var _graph: DiGraph[Identifier, SimpleEdge[Identifier]] = _
  def graph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    if (_graph eq null) {
      var g = DiGraph[Identifier, SimpleEdge[Identifier]]()

      for ((_, fd) <- symbols.functions; (from, to) <- collect(collectCalls(fd))(fd.fullBody)) {
        g += SimpleEdge(from, to)
      }

      _graph = g
    }
    _graph
  }

  def allCalls = graph.E.map(e => e._1 -> e._2)

  def isRecursive(id: Identifier) = {
    graph.transitiveSucc(id) contains id
  }

  def isSelfRecursive(id: Identifier) = {
    graph.succ(id) contains id
  }

  def calls(from: Identifier, to: Identifier) = {
    graph.E contains SimpleEdge(from, to)
  }

  def callers(to: Identifier): Set[Identifier] = {
    graph.pred(to)
  }

  def callers(tos: Set[Identifier]): Set[Identifier] = {
    tos.flatMap(callers)
  }

  def callees(from: Identifier): Set[Identifier] = {
    graph.succ(from)
  }

  def callees(froms: Set[Identifier]): Set[Identifier] = {
    froms.flatMap(callees)
  }

  def transitiveCallers(to: Identifier): Set[Identifier] = {
    graph.transitivePred(to)
  }

  def transitiveCallers(tos: Set[Identifier]): Set[Identifier] = {
    tos.flatMap(transitiveCallers)
  }

  def transitiveCallees(from: Identifier): Set[Identifier] = {
    graph.transitiveSucc(from)
  }

  def transitiveCallees(froms: Set[Identifier]): Set[Identifier] = {
    froms.flatMap(transitiveCallees)
  }

  def transitivelyCalls(from: Identifier, to: Identifier): Boolean = {
    graph.transitiveSucc(from) contains to
  }

  private[this] var _sccs: DiGraph[Set[Identifier], SimpleEdge[Set[Identifier]]] = _
  def sccs: DiGraph[Set[Identifier], SimpleEdge[Set[Identifier]]] = {
    if (_sccs eq null) {
      _sccs = graph.stronglyConnectedComponents
    }
    _sccs
  }

  object CallGraphOrderings {
    implicit object componentOrdering extends Ordering[Set[FunDef]] {
      private val components = sccs.topSort.zipWithIndex.map {
        case (ids, i) => ids.map(symbols.getFunction(_)) -> i
      }.toMap.withDefaultValue(-1)

      def compare(a: Set[FunDef], b: Set[FunDef]): Int = {
        components(a).compare(components(b))
      }
    }

    implicit object functionOrdering extends Ordering[FunDef] {
      private val functionToComponent = sccs.N.flatMap { ids =>
        val fds = ids.map(symbols.getFunction(_))
        fds.map(_ -> fds)
      }.toMap.withDefaultValue(Set.empty)

      def compare(a: FunDef, b: FunDef): Int = {
        val (c1, c2) = (functionToComponent(a), functionToComponent(b))
        if (c1.isEmpty && c2.isEmpty) a.id.uniqueName.compare(b.id.uniqueName)
        else if (c1.isEmpty) -1
        else if (c2.isEmpty) +1
        else componentOrdering.compare(c1, c2)
      }
    }
  }
}
