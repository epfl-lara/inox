/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.theories.cvc.{Sets, CVC5Sets}

trait EldaricaTarget extends SMTLIBTarget with SMTSets with SMTLIBDebugger {
  val setTarget: Sets = CVC5Sets // Eldarica (and Princess) use cvc5 set syntax
}
