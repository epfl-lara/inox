/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import org.scalatest.funsuite.AnyFunSuite

import _root_.smtlib.interpreters.ProcessInterpreter

import scala.jdk.CollectionConverters._

/** The idle solver processes that solvers leave for the next ones. */
class ProcessPoolSuite extends AnyFunSuite {
  import inox.trees._
  import SolverResponses._

  // a process that only stays alive, under a key of its own so that the solvers don't take it
  private class Idle extends ProcessInterpreter("cat", Array.empty[String]) {
    def alive: Boolean = process.isAlive
    // a freed process exits shortly after
    def exits: Boolean = process.waitFor(10, java.util.concurrent.TimeUnit.SECONDS)
  }

  private def freshKey(): Seq[String] = Seq("cat", java.util.UUID.randomUUID.toString)

  test("Idle processes are taken oldest first") {
    val key = freshKey()
    val (first, second) = (new Idle, new Idle)
    try {
      ProcessPool.give(key, first)
      ProcessPool.give(key, second)
      assert(ProcessPool.take(key) == Some(first))
      assert(ProcessPool.take(key) == Some(second))
      assert(ProcessPool.take(key) == None)
    } finally {
      first.free()
      second.free()
    }
  }

  test("The processes left beyond one per processor are freed") {
    val key = freshKey()
    val processes = Seq.fill(ProcessPool.maxIdle + 1)(new Idle)
    try {
      processes.foreach(ProcessPool.give(key, _))
      assert(processes.init.forall(_.alive))
      assert(processes.last.exits)
      assert(Seq.fill(ProcessPool.maxIdle)(ProcessPool.take(key)) == processes.init.map(Some(_)))
      assert(ProcessPool.take(key) == None)
    } finally processes.foreach(_.free())
  }

  // z3 by its path, so that the key of its processes is used by no other test
  private lazy val z3Path: Option[String] =
    sys.env.getOrElse("PATH", "").split(java.io.File.pathSeparator).iterator
      .map(dir => new java.io.File(dir, "z3"))
      .find(f => f.isFile && f.canExecute)
      .map(_.getAbsolutePath)

  private val program = InoxProgram(NoSymbols)
  private val x = Variable.fresh("x", IntegerType())

  private def solve(path: String, value: Int): Unit = {
    val factory = SolverFactory(s"smt-z3:$path", program, TestContext.empty)
    val solver = factory.getNewSolver()
    try {
      solver.assertCnstr(Equals(x, IntegerLiteral(value)))
      solver.check(Model) match {
        case SatWithModel(model) => assert(model.vars(x.toVal) == IntegerLiteral(value))
        case res => fail(s"Unexpected result $res")
      }
    } finally factory.reclaim(solver)
  }

  private def idle(path: String): Seq[ProcessInterpreter] =
    ProcessPool.idle.asScala.toSeq.collect {
      case (key, queue) if key.head == path => queue.synchronized(queue.asScala.toSeq)
    }.flatten

  test("A solver takes the process that the previous one left, reset") {
    val path = z3Path.getOrElse(cancel("z3 isn't available"))
    solve(path, 1)
    val Seq(left) = idle(path)
    solve(path, 2) // x is declared again, as the reset forgot it
    assert(idle(path) == Seq(left))
  }

  test("A solver frees an idle process whose reset failed, and starts another one") {
    val path = z3Path.getOrElse(cancel("z3 isn't available"))
    solve(path, 1)
    val Seq(left) = idle(path)
    left.kill() // as if the process had crashed while it was idle
    solve(path, 2)
    val Seq(started) = idle(path)
    assert(started ne left)
  }
}
