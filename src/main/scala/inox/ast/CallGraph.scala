/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import utils.Lazy
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

  /*@`inline`*/ def graph: DiGraph[Identifier, SimpleEdge[Identifier]] = _graph.get
  private[this] val _graph: Lazy[DiGraph[Identifier, SimpleEdge[Identifier]]] = Lazy({
    var g = DiGraph[Identifier, SimpleEdge[Identifier]]()
    for ((_, fd) <- symbols.functions; (from, to) <- collect(collectCalls(fd))(fd.fullBody)) {
      g += SimpleEdge(from, to)
    }
    g
  })

  def allCalls = graph.E.map(e => e._1 -> e._2)

  def isRecursive(id: Identifier): Boolean = {
    graph.transitiveSucc(id) contains id
  }

  def isSelfRecursive(id: Identifier): Boolean = {
    graph.succ(id) contains id
  }

  def calls(from: Identifier, to: Identifier): Boolean = {
    graph.E contains SimpleEdge(from, to)
  }

  def callers(to: Identifier): Set[Identifier] = {
    graph.pred(to)
  }

  def callers(to: FunDef): Set[FunDef] = {
    callers(to.id).map(symbols.getFunction(_))
  }

  def callers(tos: Set[Identifier]): Set[Identifier] = {
    tos.flatMap(callers)
  }

  def callers(tos: Set[FunDef])(implicit dummy: DummyImplicit): Set[FunDef] = {
    tos.flatMap(callers)
  }

  def callees(from: Identifier): Set[Identifier] = {
    graph.succ(from)
  }

  def callees(from: FunDef): Set[FunDef] = {
    callees(from.id).map(symbols.getFunction(_))
  }

  def callees(froms: Set[Identifier]): Set[Identifier] = {
    froms.flatMap(callees)
  }

  def callees(froms: Set[FunDef])(implicit dummy: DummyImplicit): Set[FunDef] = {
    froms.flatMap(callees)
  }

  def transitiveCallers(to: Identifier): Set[Identifier] = {
    graph.transitivePred(to)
  }

  def transitiveCallers(to: FunDef): Set[FunDef] = {
    transitiveCallers(to.id).map(symbols.getFunction(_))
  }

  def transitiveCallers(tos: Set[Identifier]): Set[Identifier] = {
    tos.flatMap(transitiveCallers)
  }

  def transitiveCallers(tos: Set[FunDef])(implicit dummy: DummyImplicit): Set[FunDef] = {
    tos.flatMap(transitiveCallers)
  }

  def transitiveCallees(from: Identifier): Set[Identifier] = {
    graph.transitiveSucc(from)
  }

  def transitiveCallees(from: FunDef): Set[FunDef] = {
    transitiveCallees(from.id).map(symbols.getFunction(_))
  }

  def transitiveCallees(froms: Set[Identifier]): Set[Identifier] = {
    froms.flatMap(transitiveCallees)
  }

  def transitiveCallees(froms: Set[FunDef])(implicit dummy: DummyImplicit): Set[FunDef] = {
    froms.flatMap(transitiveCallees)
  }

  def transitivelyCalls(from: Identifier, to: Identifier): Boolean = {
    graph.transitiveSucc(from) contains to
  }

  def transitivelyCalls(from: FunDef, to: FunDef): Boolean = {
    transitivelyCalls(from.id, to.id)
  }

  /*@`inline`*/ def sccs: DiGraph[Set[Identifier], SimpleEdge[Set[Identifier]]] = _sccs.get
  private[this] val _sccs: Lazy[DiGraph[Set[Identifier], SimpleEdge[Set[Identifier]]]] =
    Lazy(graph.stronglyConnectedComponents)

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
