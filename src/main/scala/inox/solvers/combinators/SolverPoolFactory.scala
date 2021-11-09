/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

import scala.collection.mutable.Queue

/**
 * This is a straitforward implementation of solver pools. The goal is to avoid
 * the cost of spawing processes for SMT solvers.
 *
 * Sadly smt-z3 is the only SMT solver that supports reset.
 *
 * If necessary, we may want to implement async reclaim/reset,
 * growing/shrinking pool size...
 */

class SolverPoolFactory private(val factory: SolverFactory)
                               (override val program: factory.program.type, override val name: String)
  extends SolverFactory { self =>
  type S = factory.S

  def this(factory: SolverFactory) = this(factory)(factory.program, "Pool(" + factory.name + ")")

  var poolSize    = 0
  val poolMaxSize = 5

  private[this] val availables = Queue[S]()
  private[this] var inUse      = Set[S]()

  def getNewSolver(): S = {
    if (availables.isEmpty) {
      poolSize += 1
      availables += factory.getNewSolver()
    }

    val s = availables.dequeue()
    inUse += s
    s
  }

  override def reclaim(s: S) = {
    try {
      s.reset()
      inUse -= s
      s.reset()
      availables += s.asInstanceOf[S]
    } catch {
      case _: CantResetException =>
        inUse -= s
        s.free()
        factory.reclaim(s)
        availables += factory.getNewSolver()
    }
  }

  def init(): Unit = {
    for (i <- 1 to poolMaxSize) {
      availables += factory.getNewSolver()
    }

    poolSize = poolMaxSize
  }

  override def shutdown(): Unit = {
    for (s <- availables ++ inUse) {
      factory.reclaim(s)
    }

    availables.clear()

    inUse      = Set()
  }

  init()
}

object SolverPoolFactory {
  def apply(sf: SolverFactory): SolverPoolFactory {
    val factory: sf.type
  } = {
    class Impl(override val factory: sf.type) extends SolverPoolFactory(factory)
    new Impl(sf)
  }
}
