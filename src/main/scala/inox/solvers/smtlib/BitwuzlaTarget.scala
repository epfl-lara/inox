package inox
package solvers
package smtlib

import _root_.smtlib.trees.Commands.*
import _root_.smtlib.interpreters.*

trait BitwuzlaTarget extends SMTLIBTarget with SMTLIBDebugger {

  import context.{*, given}

  def targetName = "bitwuzla"

  override protected val interpreter: ProcessInterpreter = {
    val opts = interpreterOpts
    reporter.debug("Invoking solver with " + opts.mkString(" "))
    new BitwuzlaInterpreter("bitwuzla", opts.toArray)
  }
}
