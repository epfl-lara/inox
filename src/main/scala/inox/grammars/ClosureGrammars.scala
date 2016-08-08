/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package grammars

trait ClosureGrammars { self: GrammarsUniverse =>
  import program._
  import trees._
  import symbols._

  case object Closures extends ExpressionGrammar {
    def computeProductions(lab: Label): Seq[ProductionRule[Label, Expr]] = lab.getType match {
      case FunctionType(argsTpes, ret) =>
        val args = argsTpes.zipWithIndex.map { case (tpe, i) =>
          ValDef(FreshIdentifier("a"+i), tpe)
        }

        val rlab = Label(ret).withAspect(ExtraTerminals(args.map(_.toVariable).toSet))

        applyAspects(lab, List(
          ProductionRule(List(rlab), { case List(body) => Lambda(args, body) }, Top, 1)
        ))

      case _ =>
        Nil
    }
  }
}
