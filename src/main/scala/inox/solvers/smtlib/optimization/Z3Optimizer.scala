/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib
package optimization

import Commands._

trait Z3Optimizer extends Z3Solver with Optimizer {
  import program._
  import program.trees._
  import program.symbols._

  def assertCnstr(expr: Expr, weight: Int): Unit = {
    exprOps.variablesOf(expr).foreach(declareVariable)

    val term = toSMT(expr)(Map())
    emit(AssertSoft(term, Some(weight), None))
  }

  def assertCnstr(expr: Expr, weight: Int, group: String): Unit = {
    exprOps.variablesOf(expr).foreach(declareVariable)

    val term = toSMT(expr)(Map())
    emit(AssertSoft(term, Some(weight), Some(group)))
  }
}
