/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

/** A [[Collector]] that collects path conditions */
trait CollectorWithPC extends TransformerWithPC with Collector

object CollectorWithPC {
  def apply[T](p: Program)(f: PartialFunction[(p.trees.Expr, p.symbols.Path), T]) = {
    new CollectorWithPC {

      type R = T
      val program: p.type = p
      import program._
      import symbols._
      import trees._
      val initEnv: Path = Path.empty

      protected def step(e: Expr, env: Path): List[(T, Path)] = {
        f.lift((e, env)).map((_, env)).toList
      }

    }
  }
}
