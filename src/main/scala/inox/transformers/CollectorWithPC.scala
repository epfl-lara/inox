/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

/** A [[Collector]] that collects path conditions */
trait CollectorWithPC extends TransformerWithPC with Collector

object CollectorWithPC {
  def apply[T](p: Program)(f: PartialFunction[(p.trees.Expr, p.symbols.Path), T]) = {
    new CollectorWithPC {

      type R = T
      val trees: p.trees.type = p.trees
      val symbols: p.symbols.type = p.symbols
      import trees.Expr
      import symbols.Path
      val initEnv: Path = Path.empty

      protected def step(e: Expr, env: Path): List[(T, Path)] = {
        f.lift((e, env)).map((_, env)).toList
      }

    }
  }
}
