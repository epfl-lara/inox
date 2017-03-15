/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.smtlib.optimization

import smtlib.printer._
import smtlib.parser.Terms._
import smtlib.parser.Commands._

object Commands {

  case class Maximize(term: Term) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(maximize ")
      ctx.print(term)
      ctx.print(")")
    }
  }

  case class Minimize(term: Term) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(minimize ")
      ctx.print(term)
      ctx.print(")")
    }
  }

  case class AssertSoft(term: Term, optWeight: Option[Int], optGroup: Option[String]) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
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
  }
}
