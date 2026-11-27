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

  protected trait Collector extends SelfTreeTraverser {
    private var ids: Set[Identifier] = Set.empty

    protected def register(id: Identifier): Unit = ids += id
    def result: Set[Identifier] = ids
  }
  // Used as a default implementation for the trait Collector
  protected class ConcreteCollector extends ConcreteSelfTreeTraverser with Collector

  protected trait FunctionCollector extends Collector {
    override def traverse(expr: Expr): Unit = expr match {
      case FunctionInvocation(id, _, _) =>
        register(id)
        super.traverse(expr)
      case _ =>
        super.traverse(expr)
    }
  }
  // Used as a default implementation for the trait FunctionCollector
  protected class ConcreteFunctionCollector extends ConcreteSelfTreeTraverser with FunctionCollector

  protected def getFunctionCollector: Collector = new ConcreteFunctionCollector

  private def collectCalls(fd: FunDef): Set[Identifier] = {
    val collector = getFunctionCollector
    collector.traverse(fd)
    collector.result
  }

  protected def computeCallGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = DiGraph[Identifier, SimpleEdge[Identifier]]()
    for ((_, fd) <- symbols.functions; id <- collectCalls(fd)) {
      g += SimpleEdge(fd.id, id)
    }
    g
  }

  /** The function `id` and the functions it calls transitively. Unlike [[transitiveCallees]], this only
    * visits the functions that `id` reaches instead of computing the call graph of the whole program. */
  def reachableFunctions(id: Identifier): Set[Identifier] = {
    var seen = Set(id)
    var todo = List(id)
    while (todo.nonEmpty) {
      val fid = todo.head
      todo = todo.tail
      for (callee <- collectCalls(symbols.getFunction(fid)) if !seen(callee)) {
        seen += callee
        todo = callee :: todo
      }
    }
    seen
  }

  @inline def callGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = _callGraph.get
  private val _callGraph: Lazy[DiGraph[Identifier, SimpleEdge[Identifier]]] = Lazy(computeCallGraph)

  def allCalls = callGraph.E.map(e => e._1 -> e._2)

  def isRecursive(id: Identifier): Boolean =
    callGraph.transitiveSucc(id) contains id

  def isSelfRecursive(id: Identifier): Boolean =
    callGraph.succ(id) contains id

  def calls(from: Identifier, to: Identifier): Boolean =
    callGraph.E contains SimpleEdge(from, to)

  def callers(to: Identifier): Set[Identifier] =
    callGraph.pred(to)

  def callers(to: FunDef): Set[FunDef] =
    callers(to.id).map(symbols.getFunction(_))

  def callers(tos: Set[Identifier]): Set[Identifier] =
    tos.flatMap(callers)

  def callers(tos: Set[FunDef])(using DummyImplicit): Set[FunDef] =
    tos.flatMap(callers)

  def callees(from: Identifier): Set[Identifier] =
    callGraph.succ(from)

  def callees(from: FunDef): Set[FunDef] =
    callees(from.id).map(symbols.getFunction(_))

  def callees(froms: Set[Identifier]): Set[Identifier] =
    froms.flatMap(callees)

  def callees(froms: Set[FunDef])(using DummyImplicit): Set[FunDef] =
    froms.flatMap(callees)

  def transitiveCallers(to: Identifier): Set[Identifier] =
    callGraph.transitivePred(to)

  def transitiveCallers(to: FunDef): Set[FunDef] =
    transitiveCallers(to.id).map(symbols.getFunction(_))

  def transitiveCallers(tos: Set[Identifier]): Set[Identifier] =
    tos.flatMap(transitiveCallers)

  def transitiveCallers(tos: Set[FunDef])(using DummyImplicit): Set[FunDef] =
    tos.flatMap(transitiveCallers)

  def transitiveCallees(from: Identifier): Set[Identifier] =
    callGraph.transitiveSucc(from)

  def transitiveCallees(from: FunDef): Set[FunDef] =
    transitiveCallees(from.id).map(symbols.getFunction(_))

  def transitiveCallees(froms: Set[Identifier]): Set[Identifier] =
    froms.flatMap(transitiveCallees)

  def transitiveCallees(froms: Set[FunDef])(using DummyImplicit): Set[FunDef] =
    froms.flatMap(transitiveCallees)

  def transitivelyCalls(from: Identifier, to: Identifier): Boolean =
    callGraph.transitiveSucc(from) contains to

  def transitivelyCalls(from: FunDef, to: FunDef): Boolean =
    transitivelyCalls(from.id, to.id)

  @inline def sccs: DiGraph[Set[Identifier], SimpleEdge[Set[Identifier]]] = _sccs.get
  private val _sccs: Lazy[DiGraph[Set[Identifier], SimpleEdge[Set[Identifier]]]] =
    Lazy(callGraph.stronglyConnectedComponents)

  object CallGraphOrderings {
    given componentOrdering: Ordering[Set[FunDef]] with
      // A topological order of the components, callers first, that doesn't depend on the hashes of
      // identifiers: among the components whose callers all come before, the one with the smallest
      // identifier comes first.
      private val components = {
        val graph = sccs
        val key: Set[Identifier] => Identifier = _.min
        var callers = graph.N.map(n => n -> (graph.pred(n) - n).size).toMap
        val ready = scala.collection.mutable.PriorityQueue.empty[Set[Identifier]](using Ordering.by(key).reverse)
        ready ++= graph.N.filter(callers(_) == 0)
        val order = scala.collection.mutable.ArrayBuffer.empty[Set[Identifier]]
        while (ready.nonEmpty) {
          val n = ready.dequeue()
          order += n
          for (m <- graph.succ(n) if m != n) {
            callers += m -> (callers(m) - 1)
            if (callers(m) == 0) ready += m
          }
        }
        order.zipWithIndex.map { case (ids, i) => ids.map(symbols.getFunction(_)) -> i }.toMap.withDefaultValue(-1)
      }

      def compare(a: Set[FunDef], b: Set[FunDef]): Int = {
        components(a).compare(components(b))
      }

    given functionOrdering: Ordering[FunDef] with
      private val functionToComponent = sccs.N.flatMap { ids =>
        val fds = ids.map(symbols.getFunction(_))
        fds.map(_ -> fds)
      }.toMap.withDefaultValue(Set.empty)

      def compare(a: FunDef, b: FunDef): Int = {
        val (c1, c2) = (functionToComponent(a), functionToComponent(b))
        if (c1.isEmpty && c2.isEmpty) a.id.compare(b.id)
        else if (c1.isEmpty) -1
        else if (c2.isEmpty) +1
        else {
          val comp = componentOrdering.compare(c1, c2)
          // the functions of a component, by identifier
          if (comp != 0) comp else a.id.compare(b.id)
        }
      }
  }
}
