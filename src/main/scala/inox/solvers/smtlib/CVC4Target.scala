/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.trees.Commands._
import _root_.smtlib.interpreters._
import _root_.smtlib.theories._
import _root_.smtlib.theories.cvc._

trait CVC4Target extends CVCTarget {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  def targetName = "cvc4"

  override protected val interpreter: ProcessInterpreter = {
    val opts = interpreterOpts
    reporter.debug("Invoking solver with "+opts.mkString(" "))
    new CVC4Interpreter("cvc4", opts.toArray)
  }

  // CVC5 emits a warning when no (set-logic X) command is passed
  // So we emit (set-logic all) by default for all solvers
  emit(SetLogic(ALL()))


  override val cvcSets: Sets = CVC4Sets
}
