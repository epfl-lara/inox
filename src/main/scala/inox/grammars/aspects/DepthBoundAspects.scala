/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package grammars
package aspects

trait DepthBoundAspects { self: GrammarsUniverse =>
  import program.trees.PrinterOptions

  /** Limits a grammar by depth */
  case class DepthBound(depth: Int) extends Aspect {
    require(depth >= 0)

    def asString(implicit opts: PrinterOptions): String = s"D$depth"

    def applyTo(l: Label, ps: Seq[Production])(implicit ctx: InoxContext) = {
      if (depth == 0) Nil
      else if (depth == 1) ps.filter(_.isTerminal)
      else {
        ps map { prod =>
          prod.copy(subTrees = prod.subTrees.map(_.withAspect(DepthBound(depth - 1))))
        }
      }
    }
  }
}

