/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

/** A common trait for objects that collect something from expressions.
  * This trait is meant to be mixed in with a specific [[Transformer]] to attach collect functionality.
  */
trait Collector extends Transformer {
  /** The type of collected objects */
  type Result
  private var results: List[Result] = Nil

  import trees._

  protected def accumulate(e: Expr, env: Env): Unit = {
    results ++= step(e, env)
  }

  /** Does one step of collection for the current [[ast.Expressions.Expr Expr]] and [[Env]] */
  protected def step(e: Expr, env: Env): List[Result]

  abstract override protected def rec(e: Expr, current: Env): Expr = {
    accumulate(e, current)
    super.rec(e, current)
  }

  /** Traverses an [[ast.Expressions.Expr Expr]] with the specified environment and collects */
  final def collect(e: Expr, init: Env) = {
    results = Nil
    transform(e, init)
    results
  }

  /** Traverses an [[ast.Expressions.Expr Expr]] with the initial environment and collects */
  final def collect(e: Expr): List[Result] = collect(e, initEnv)

  /** Collect the expressions in a [[ast.Definitions.FunDef FunDef]]'s body */
  final def collect(fd: FunDef): List[Result] = collect(fd.fullBody)
}
