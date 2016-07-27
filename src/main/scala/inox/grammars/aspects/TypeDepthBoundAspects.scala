/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package grammars
package aspects

trait TypeDepthBoundAspects { self: GrammarsUniverse =>
  import program._
  import trees._
  import symbols.typeOps.depth

  case class TypeDepthBound(bound: Int) extends PersistentAspect {
    override def asString(implicit opts: PrinterOptions): String = "" // This is just debug pollution to print

    override def applyTo(lab: Label, ps: Seq[Production])(implicit ctx: InoxContext) = {
      if (depth(lab.getType) > bound) Nil
      else super.applyTo(lab, ps)
    }

  }
}
