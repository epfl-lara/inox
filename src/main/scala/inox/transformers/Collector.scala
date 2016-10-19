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

  /** Does one step of collection for the current [[Expr]] and [[Env]] */
  protected def step(e: Expr, env: Env): List[Result]

  abstract override protected def rec(e: Expr, current: Env): Expr = {
    results ++= step(e, current)
    super.rec(e, current)
  }

  /** Traverses the expression and collects */
  final def collect(e: Expr): List[Result] = {
    results = Nil
    transform(e)
    results
  }

  /** Collect the expressions in a [[FunDef]]'s body */
  final def collect(fd: FunDef): List[Result] = collect(fd.fullBody)
}
