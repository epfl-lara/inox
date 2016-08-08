/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package grammars
package aspects

trait ExtraTerminalsAspects { self: GrammarsUniverse =>
  import program._
  import trees._
  import exprOps.formulaSize
  import symbols._

  /**
   * Informs sub-productions that there are extra terminals available (used by
   * grammars.ExtraTerminals).
   */
  case class ExtraTerminals(s: Set[Expr]) extends PersistentAspect {
    def asString(implicit opts: PrinterOptions) = {
      s.toList.map(_.asString(opts)).mkString("{", ",", "}")
    }

    override def applyTo(lab: Label, ps: Seq[Production]) = {
      super.applyTo(lab, ps) ++ {
        s.filter(e => isSubtypeOf(e.getType, lab.getType)).map { e =>
          ProductionRule[Label, Expr](Nil, { (es: Seq[Expr]) => e }, Top, formulaSize(e))
        }
      }
    }
  }
}

