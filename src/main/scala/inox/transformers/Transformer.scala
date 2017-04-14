/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

import ast._

/** Common trait for expression transformers.
  * Uses an abstract environment type.
  */
trait Transformer {
  type Env
  val trees: Trees
  import trees.{Expr, FunDef}

  /** The default initial [[Env]] */
  def initEnv: Env

  /** The function that recursively traverses the expression
    *
    * @param e The current expression
    * @param env The current [[Env]]
    * @return The transformed expression
    */
  protected def rec(e: Expr, env: Env): Expr

  /** Transform an [[ast.Expressions.Expr Expr]] with the specified environment */
  final def transform(e: Expr, init: Env): Expr = rec(e, init)
  /** Transform an [[ast.Expressions.Expr Expr]] with the initial environment */
  final def transform(e: Expr): Expr            = transform(e, initEnv)
  /** Transform the body of a [[ast.Definitions.FunDef FunDef]] */
  final def transform(fd: FunDef): Expr         = transform(fd.fullBody)
}

