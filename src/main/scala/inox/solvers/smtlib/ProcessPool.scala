/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.interpreters.ProcessInterpreter

import java.util.ArrayDeque
import java.util.concurrent.ConcurrentHashMap

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
  private[smtlib] val maxIdle = Runtime.getRuntime.availableProcessors.max(1)

  // each queue is only accessed while holding its lock, so that `give` never exceeds `maxIdle`
  private[smtlib] val idle = new ConcurrentHashMap[Seq[String], ArrayDeque[ProcessInterpreter]]

  private def processes(key: Seq[String]): ArrayDeque[ProcessInterpreter] =
    idle.computeIfAbsent(key, _ => new ArrayDeque[ProcessInterpreter])

  /** An idle process started with the command line `key`, which the caller now owns.
    *
    * The process that was left here first is taken first, as it had the most time to reset. */
  def take(key: Seq[String]): Option[ProcessInterpreter] = {
    val queue = processes(key)
    Option(queue.synchronized(queue.pollFirst()))
  }

  /** Leaves the idle process `interpreter`, started with the command line `key` and reset (or
    * being reset) by the caller, for another solver. */
  def give(key: Seq[String], interpreter: ProcessInterpreter): Unit = {
    val queue = processes(key)
    val kept = queue.synchronized {
      queue.size < maxIdle && { queue.addLast(interpreter); true }
    }
    // freed outside of the lock, so that the other solvers don't wait for it
    if (!kept) interpreter.free()
  }
}
