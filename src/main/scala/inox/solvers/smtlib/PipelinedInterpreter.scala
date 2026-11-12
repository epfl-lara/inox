/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.interpreters.{BitwuzlaInterpreter, CVC4Interpreter, CVC5Interpreter, ProcessInterpreter, Z3Interpreter}
import _root_.smtlib.parser.Parser
import _root_.smtlib.trees.Terms.SExpr
import _root_.smtlib.trees.Commands._
import _root_.smtlib.trees.CommandsResponses.{Error => SMTError, _}

import java.io.BufferedReader

/** A solver process that doesn't wait for the `success` of the commands that only answer that.
  *
  * Each command is otherwise a round trip to the process, and most commands are declarations and
  * assertions, which solvers handle in a few microseconds. [[send]] buffers such a command without
  * reading its answer, and the pending answers are read before the next command that is evaluated
  * (see [[eval]]). An error that one of them answered is then returned by [[pendingError]].
  *
  * The solver must answer `success` to these commands (`:print-success`).
  *
  * The commands that are sent are written to the process by another thread (see
  * [[PipelinedInterpreter.writers]]), while the answers are read by the thread of the solver: the
  * process blocks once the pipe of its output is full, and stops reading its input, so that a
  * thread that both writes the commands and reads their answers could wait on the process while
  * the process waits on it. This happens even with few commands when their answers are longer
  * than the commands themselves, such as errors, or when the pipes are small (16 KiB on macOS).
  */
trait PipelinedInterpreter extends ProcessInterpreter {

  private var pending = 0
  private var error: Option[String] = None

  // the commands that were sent and not yet handed to a writer
  private val buffer = new java.io.StringWriter

  // the commands that were handed to a writer, and whether one is writing them (both guarded by
  // `writes`), as well as the exception of the writes, if any
  private val writes = new java.util.ArrayDeque[String]
  private var writing = false
  @volatile private var writeError: Option[String] = None

  /** Whether `cmd` only answers `success` (or an error), so that it can be sent with [[send]]. */
  def pipelines(cmd: SExpr): Boolean = cmd match {
    case _: DeclareFun | _: DeclareConst | _: DeclareSort | _: DefineSort | _: DeclareDatatypes | _: Assert => true
    case _ => false
  }

  /** Buffers `cmd`, whose answer is read before the next command that is evaluated. */
  def send(cmd: SExpr): Unit = {
    printer.printSExpr(cmd, buffer)
    buffer.write("\n")
    pending += 1
    if (buffer.getBuffer.length >= PipelinedInterpreter.ChunkSize) handOff()
  }

  // has a writer write the commands of `buffer` to the process
  private def handOff(): Unit = if (buffer.getBuffer.length > 0) {
    val chunk = buffer.toString
    buffer.getBuffer.setLength(0)
    writes.synchronized {
      writes.addLast(chunk)
      if (!writing) {
        writing = true
        PipelinedInterpreter.writers.execute(() => write())
      }
    }
  }

  // writes the commands handed to the writers, until there are none
  private def write(): Unit = {
    var done = false
    while (!done) {
      val chunk = writes.synchronized {
        val chunk = writes.pollFirst()
        if (chunk == null) {
          writing = false
          writes.notifyAll()
          done = true
        }
        chunk
      }
      if (chunk != null) try {
        in.write(chunk)
        in.flush()
      } catch {
        // as `eval` does, for instance once the process was killed by an interrupt
        case e: Exception =>
          if (writeError.isEmpty) writeError = Some("Solver encountered exception: " + e)
          writes.synchronized(writes.clear())
      }
    }
  }

  /** Reads the answers of the commands that were sent and not yet answered. */
  def flush(): Unit = if (pending > 0) {
    handOff()
    try {
      while (pending > 0) {
        pending -= 1
        parser.parseGenResponse match {
          case SMTError(msg) => recordError(msg)
          case _ =>
        }
      }
      // all the commands were answered, so that they were all written
      writes.synchronized(while (writing) writes.wait())
    } catch {
      case e: Exception =>
        pending = 0
        recordError("Solver encountered exception: " + e)
        // the answers can't be told apart anymore, and a writer could wait on the process forever
        kill()
    }
    writeError.foreach(recordError)
    writeError = None
  }

  private def recordError(msg: String): Unit = if (error.isEmpty) error = Some(msg)

  /** The first error answered by a sent command since the last call, if any. */
  def pendingError(): Option[String] = {
    val res = error
    error = None
    res
  }

  override def eval(cmd: SExpr): SExpr = {
    flush()
    // a reset forgets the commands that were sent, and their errors with them: the process can
    // then be left in the pool (see [[ProcessPool]]) without an error for the next solver
    if (cmd == Reset()) error = None
    super.eval(cmd)
  }

  override def free(): Unit = {
    // a writer could be waiting on the process, which then doesn't read its `(exit)`
    if (writes.synchronized(writing)) kill()
    else super.free()
  }
}

object PipelinedInterpreter {
  /** The size of the chunks of commands that the writers write at once. */
  private val ChunkSize = 8192

  /** The threads that write the commands that are sent, which are created as needed. */
  private val writers = java.util.concurrent.Executors.newCachedThreadPool { (task: Runnable) =>
    // the thread only writes, so that a small stack is enough (the default can be large)
    val thread = new Thread(null, task, "smtlib-writer", 256 * 1024)
    thread.setDaemon(true)
    thread
  }
}

class PipelinedZ3Interpreter(executable: String, args: Array[String], parserCtor: BufferedReader => Parser)
  extends Z3Interpreter(executable, args, parserCtor = parserCtor) with PipelinedInterpreter

class PipelinedCVC4Interpreter(executable: String, args: Array[String])
  extends CVC4Interpreter(executable, args) with PipelinedInterpreter

class PipelinedCVC5Interpreter(executable: String, args: Array[String])
  extends CVC5Interpreter(executable, args) with PipelinedInterpreter

class PipelinedBitwuzlaInterpreter(executable: String, args: Array[String])
  extends BitwuzlaInterpreter(executable, args) with PipelinedInterpreter
