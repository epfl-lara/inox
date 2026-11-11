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
  * assertions, which solvers handle in a few microseconds. [[send]] writes such a command without
  * reading its answer, and the pending answers are read before the next command that is evaluated
  * (see [[eval]]). An error that one of them answered is then returned by [[pendingError]].
  *
  * The solver must answer `success` to these commands (`:print-success`).
  *
  * The answers that are already available are read before each command is sent: the solver
  * blocks once the pipe of its output is full, and stops reading its input, so that writing more
  * commands would then block too.
  */
trait PipelinedInterpreter extends ProcessInterpreter {

  private var pending = 0
  private var error: Option[String] = None

  /** Whether `cmd` only answers `success` (or an error), so that it can be sent with [[send]]. */
  def pipelines(cmd: SExpr): Boolean = cmd match {
    case _: DeclareFun | _: DeclareConst | _: DeclareSort | _: DefineSort | _: DeclareDatatypes | _: Assert => true
    case _ => false
  }

  /** Writes `cmd`, whose answer is read before the next command that is evaluated. */
  def send(cmd: SExpr): Unit = {
    try {
      while (pending > 0 && answerReady()) readAnswer()
      printer.printSExpr(cmd, in)
      in.write("\n")
      pending += 1
    } catch {
      // as `eval` does, for instance once the process was killed by an interrupt
      case e: Exception =>
        pending = 0
        recordError("Solver encountered exception: " + e)
    }
  }

  /** Reads the answers of the commands that were sent and not yet answered. */
  def flush(): Unit = if (pending > 0) {
    try {
      in.flush()
      while (pending > 0) readAnswer()
    } catch {
      case e: Exception =>
        pending = 0
        recordError("Solver encountered exception: " + e)
    }
  }

  private def readAnswer(): Unit = {
    pending -= 1
    parser.parseGenResponse match {
      case SMTError(msg) => recordError(msg)
      case _ =>
    }
  }

  /** Whether the solver started writing an answer, so that reading it doesn't wait for the solver.
    *
    * The line ends that follow the answers that were read are skipped, without waiting either.
    */
  private def answerReady(): Boolean = {
    out.mark(1)
    var c = if (out.ready()) out.read() else -2
    while (c == ' ' || c == '\n' || c == '\r' || c == '\t') {
      out.mark(1)
      c = if (out.ready()) out.read() else -2
    }
    if (c >= 0) out.reset()
    c != -2
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
}

class PipelinedZ3Interpreter(executable: String, args: Array[String], parserCtor: BufferedReader => Parser)
  extends Z3Interpreter(executable, args, parserCtor = parserCtor) with PipelinedInterpreter

class PipelinedCVC4Interpreter(executable: String, args: Array[String])
  extends CVC4Interpreter(executable, args) with PipelinedInterpreter

class PipelinedCVC5Interpreter(executable: String, args: Array[String])
  extends CVC5Interpreter(executable, args) with PipelinedInterpreter

class PipelinedBitwuzlaInterpreter(executable: String, args: Array[String])
  extends BitwuzlaInterpreter(executable, args) with PipelinedInterpreter
