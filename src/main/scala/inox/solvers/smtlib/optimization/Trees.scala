/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.smtlib.optimization

import smtlib.printer._
import smtlib.trees.Terms._
import smtlib.trees.TreeTransformer
import smtlib.trees.Commands._

object Commands {

  case class Maximize(term: Term) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(maximize ")
      ctx.print(term)
      ctx.print(")")
    }

    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ??? // FIXME
  }

  case class Minimize(term: Term) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(minimize ")
      ctx.print(term)
      ctx.print(")")
    }

    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ??? // FIXME
  }

  case class AssertSoft(term: Term, optWeight: Option[Int], optGroup: Option[String]) extends CommandExtension {
    override def print(ctx: PrintingContext): Unit = {
      ctx.print("(assert-soft ")
      ctx.print(term)
      if (optWeight.isDefined) {
        ctx.print(" :weight ")
        ctx.print(optWeight.get.toString)
      }
      if (optGroup.isDefined) {
        ctx.print(" :id ")
        ctx.print(optGroup.get)
      }
      ctx.print(")")
    }

    override def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ??? // FIXME
  }
}
