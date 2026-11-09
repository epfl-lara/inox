/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers.z3

import z3.scala.{Z3Optimizer => ScalaZ3Optimizer, _}
import Z3Native._
import solvers._
import unrolling._

trait NativeZ3Optimizer extends Z3Unrolling with AbstractUnrollingOptimizer  { self =>

  import program._
  import program.trees._
  import program.symbols.{given, _}

  override val name = "native-z3-opt"

  override protected val underlying = Z3Native.lock.synchronized(new Underlying(targetProgram, context)(using targetSemantics))

  private type Target = targetProgram.type

  private class Underlying(override val program: Target,
                           override val context: Context)
                          (using override val semantics: targetSemantics.type)
    extends AbstractOptimizer with Z3Native {
    import program._
    import program.trees._
    import program.symbols.{given, _}

    import SolverResponses._

    val name = "z3-opt"

    private val optimizer: ScalaZ3Optimizer = z3.mkOptimizer()
    private val defaultGroup = "inox$default"

    def assertCnstr(ast: Z3AST): Unit = tryZ3(optimizer.assertCnstr(ast))
    // ScalaZ3 puts each ungrouped soft constraint in a fresh group of its own, which
    // makes Z3 optimize them one after the other instead of weighing them against each
    // other. Share one group between them, as SMT-LIB does for `assert-soft` without an id.
    def assertCnstr(ast: Z3AST, weight: Int): Unit = tryZ3(optimizer.assertCnstr(ast, weight, defaultGroup))
    def assertCnstr(ast: Z3AST, weight: Int, group: String): Unit = tryZ3(optimizer.assertCnstr(ast, weight, group))

    def maximize(ast: Z3AST): Unit = tryZ3(optimizer.maximize(ast))
    def minimize(ast: Z3AST): Unit = tryZ3(optimizer.minimize(ast))

    // NOTE @nv: this is very similar to code in AbstractZ3Solver and UninterpretedZ3Solver but
    //           is difficult to merge due to small API differences between the native Z3
    //           solvers and optimizers.
    private def checkOptimizer(config: Configuration): config.Response[Model, Assumptions] =
      config.cast(tryZ3[SolverResponse[Model, Assumptions]](optimizer.check() match {
        case Some(true) => if (config.withModel) SatWithModel(optimizer.getModel()) else Sat
        case Some(false) => if (config.withUnsatAssumptions) UnsatWithAssumptions(Set()) else Unsat
        case None => Unknown
      }).getOrElse(Unknown))

    def check(config: CheckConfiguration): config.Response[Model, Assumptions] = checkOptimizer(config)

    // The optimizer has no assumptions of its own: assert them in a scope of their own.
    def checkAssumptions(config: Configuration)(assumptions: Set[Z3AST]): config.Response[Model, Assumptions] = {
      val pushed = tryZ3(optimizer.push()).isDefined
      for (a <- assumptions) assertCnstr(a)
      val res = checkOptimizer(config)
      if (pushed) tryZ3(optimizer.pop())
      res
    }

    // See AbstractZ3Solver: an interrupted push or pop throws.
    private var z3Scopes: List[Boolean] = Nil

    override def push(): Unit = {
      super.push()
      z3Scopes = tryZ3(optimizer.push()).isDefined :: z3Scopes
    }

    override def pop(): Unit = {
      super.pop()
      val pushed = z3Scopes.headOption.getOrElse(true)
      z3Scopes = z3Scopes.drop(1)
      if (pushed) tryZ3(optimizer.pop())
    }
  }

  override def free(): Unit = Z3Native.lock.synchronized(super.free())
}
