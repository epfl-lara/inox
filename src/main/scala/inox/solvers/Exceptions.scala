/* Copyright 2009-2018 EPFL, Lausanne */

package inox.solvers

class CantResetException(s: AbstractSolver) extends Exception(s"Unable to reset solver $s")

class InternalSolverError(msg: String) extends Exception(msg) {
  def this(name: String, msg: String) = this(s"Internal solver error in $name: $msg")
}
