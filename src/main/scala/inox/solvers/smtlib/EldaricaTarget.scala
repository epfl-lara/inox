/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.trees.Commands._
import _root_.smtlib.theories._
import _root_.smtlib.theories.cvc._

trait EldaricaTarget extends SMTLIBTarget with SMTLIBDebugger {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]) = super.toSMT(e)
}
