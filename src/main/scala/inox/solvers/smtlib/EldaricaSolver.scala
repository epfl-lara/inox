/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.{smtlib => sl}
import _root_.smtlib.trees.Terms.{Identifier => _, _}
import _root_.smtlib.trees.CommandsResponses._

trait EldaricaSolver extends SMTLIBSolver with EldaricaTarget {

  protected val interpreter: sl.Interpreter =
    new EldaricaInterpreter(sl.printer.RecursivePrinter, out => sl.parser.Parser(sl.extensions.tip.Lexer(out)))

  def targetName = "eldarica"

  protected def interpreterOpts: Seq[String] = Seq.empty
}
