/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.trees.Commands._
import _root_.smtlib.interpreters._
import _root_.smtlib.theories._
import _root_.smtlib.theories.cvc._

trait CVC5Target extends CVCTarget {
  import context.{*, given}
  import program.*
  import program.symbols.{*, given}
  import program.trees.*

  def targetName = "cvc5"

  override protected val interpreter: ProcessInterpreter = {
    val opts = interpreterOpts
    reporter.debug("Invoking solver with "+opts.mkString(" "))
    new CVC5Interpreter("cvc5", opts.toArray)
  }
  override val cvcSets: Sets = CVC5Sets
}
