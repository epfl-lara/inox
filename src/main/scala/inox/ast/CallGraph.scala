/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import utils.Graphs._

trait CallGraph {
  protected val trees: Trees
  import trees._
  import trees.exprOps._
  protected val symbols: Symbols

  private def collectCalls(fd: FunDef)(e: Expr): Set[(FunDef, FunDef)] = e match {
    case f @ FunctionInvocation(id, tps, _) => Set((fd, symbols.getFunction(id)))
    case _ => Set()
  }

  lazy val graph: DiGraph[FunDef, SimpleEdge[FunDef]] = {
    var g = DiGraph[FunDef, SimpleEdge[FunDef]]()

    for ((_, fd) <- symbols.functions; c <- collect(collectCalls(fd))(fd.fullBody)) {
      g += SimpleEdge(c._1, c._2)
    }

    g
  }

  lazy val allCalls = graph.E.map(e => e._1 -> e._2)

  def isRecursive(f: FunDef) = {
    graph.transitiveSucc(f) contains f
  }

  def isSelfRecursive(f: FunDef) = {
    graph.succ(f) contains f
  }

  def calls(from: FunDef, to: FunDef) = {
    graph.E contains SimpleEdge(from, to)
  }

  def callers(to: FunDef): Set[FunDef] = {
    graph.pred(to)
  }

  def callers(tos: Set[FunDef]): Set[FunDef] = {
    tos.flatMap(callers)
  }

  def callees(from: FunDef): Set[FunDef] = {
    graph.succ(from)
  }

  def callees(froms: Set[FunDef]): Set[FunDef] = {
    froms.flatMap(callees)
  }

  def transitiveCallers(to: FunDef): Set[FunDef] = {
    graph.transitivePred(to)
  }

  def transitiveCallers(tos: Set[FunDef]): Set[FunDef] = {
    tos.flatMap(transitiveCallers)
  }

  def transitiveCallees(from: FunDef): Set[FunDef] = {
    graph.transitiveSucc(from)
  }

  def transitiveCallees(froms: Set[FunDef]): Set[FunDef] = {
    froms.flatMap(transitiveCallees)
  }

  def transitivelyCalls(from: FunDef, to: FunDef): Boolean = {
    graph.transitiveSucc(from) contains to
  }

  lazy val stronglyConnectedComponents = graph.stronglyConnectedComponents.N

  lazy val functionComponent: Map[FunDef, Set[FunDef]] = {
    val inComponents = stronglyConnectedComponents.flatMap(fds => fds.map(_ -> fds)).toMap
    inComponents ++ symbols.functions.values.filterNot(inComponents.isDefinedAt).map(_ -> Set.empty[FunDef])
  }

  object CallGraphOrderings {
    implicit object componentOrdering extends Ordering[Set[FunDef]] {
      private val components = graph.stronglyConnectedComponents.topSort
      def compare(a: Set[FunDef], b: Set[FunDef]): Int = {
        components.indexOf(a).compare(components.indexOf(b))
      }
    }

    implicit object functionOrdering extends Ordering[FunDef] {
      def compare(a: FunDef, b: FunDef): Int = {
        val (c1, c2) = (functionComponent(a), functionComponent(b))
        if (c1.isEmpty && c2.isEmpty) a.id.uniqueName.compare(b.id.uniqueName)
        else if (c1.isEmpty) -1
        else if (c2.isEmpty) +1
        else componentOrdering.compare(c1, c2)
      }
    }
  }
}
