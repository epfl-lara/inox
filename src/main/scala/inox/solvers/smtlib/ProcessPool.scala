/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.interpreters.ProcessInterpreter

import java.util.concurrent.{ConcurrentHashMap, ConcurrentLinkedDeque}

/** Idle solver processes, which new solvers reuse instead of starting processes of their own.
  *
  * Starting a solver process and having it set up its first context takes several milliseconds
  * (about 10ms for Z3), which is often more than the queries of a solver take: Inox starts a
  * solver for each query, and for each quantifier it evaluates in a model. A solver that is freed
  * without having been interrupted resets its process and leaves it here for the next solver
  * started with the same command line.
  *
  * At most one idle process per processor is kept for each command line, the others are freed.
  */
object ProcessPool {
  private val maxIdle = Runtime.getRuntime.availableProcessors.max(1)

  private val idle = new ConcurrentHashMap[Seq[String], ConcurrentLinkedDeque[ProcessInterpreter]]

  private def processes(key: Seq[String]): ConcurrentLinkedDeque[ProcessInterpreter] =
    idle.computeIfAbsent(key, _ => new ConcurrentLinkedDeque[ProcessInterpreter])

  /** An idle process started with the command line `key`, which the caller now owns. */
  def take(key: Seq[String]): Option[ProcessInterpreter] = Option(processes(key).pollFirst())

  /** Leaves the idle process `interpreter`, started with the command line `key` and reset by the
    * caller, for another solver. */
  def give(key: Seq[String], interpreter: ProcessInterpreter): Unit = {
    val queue = processes(key)
    if (queue.size < maxIdle) queue.addFirst(interpreter)
    else interpreter.free()
  }
}
