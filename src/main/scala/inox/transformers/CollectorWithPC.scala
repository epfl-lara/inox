/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

/** A [[Collector]] that collects path conditions */
trait CollectorWithPC extends TransformerWithPC with Collector {
  import program.trees._
  import program.symbols._

  lazy val initEnv: Path = Path.empty
}

object CollectorWithPC {
  def apply[T](p: Program)
              (f: PartialFunction[(p.trees.Expr, p.symbols.Path), T]):
               CollectorWithPC { type Result = T; val program: p.type } = {
    new CollectorWithPC {
      type Result = T
      val program: p.type = p
      import program.trees._
      import program.symbols._

      private val fLifted = f.lift

      protected def step(e: Expr, env: Path): List[T] = {
        fLifted((e, env)).toList
      }
    }
  }

}
