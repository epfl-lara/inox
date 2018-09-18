/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

trait AbstractUnrollingOptimizer extends AbstractUnrollingSolver with Optimizer { self =>
  import program._
  import program.trees._
  import program.symbols._

  protected val underlying: AbstractOptimizer {
    val program: targetProgram.type
    type Trees = Encoded
  }

  def assertCnstr(expression: Expr, weight: Int): Unit = {
    val b = Variable.fresh("b", BooleanType())
    assertCnstr(Implies(b, expression))
    underlying.assertCnstr(freeVars(b), weight)
  }

  def assertCnstr(expression: Expr, weight: Int, group: String): Unit = {
    val b = Variable.fresh("b", BooleanType())
    assertCnstr(Implies(b, expression))
    underlying.assertCnstr(freeVars(b), weight, group)
  }
}

trait UnrollingOptimizer extends AbstractUnrollingOptimizer with UnrollingSolver {

  protected val underlying: AbstractOptimizer {
    val program: targetProgram.type
    type Trees = t.Expr
    type Model = targetProgram.Model
  }

  override lazy val name = "UO:" + underlying.name
}
