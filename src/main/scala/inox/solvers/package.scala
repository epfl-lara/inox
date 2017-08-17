/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import scala.language.implicitConversions
import scala.concurrent.duration._

package object solvers {
  import combinators._

  sealed abstract class PurityOptions {
    def assumeChecked = this != PurityOptions.Unchecked
    def totalFunctions = this == PurityOptions.TotalFunctions
  }

  object PurityOptions {
    case object Unchecked extends PurityOptions
    case object AssumeChecked extends PurityOptions
    case object TotalFunctions extends PurityOptions

    def apply(ctx: Context) = ctx.options.findOptionOrDefault(optAssumeChecked)
  }

  object optAssumeChecked extends OptionDef[PurityOptions] {
    val name = "assumechecked"
    val default = PurityOptions.Unchecked
    val parser = (str: String) => str match {
      case "false" => Some(PurityOptions.Unchecked)
      case "" | "checked" => Some(PurityOptions.AssumeChecked)
      case "total" => Some(PurityOptions.TotalFunctions)
      case _ => None
    }
    val usageRhs = s"--$name=(false|checked|total)"
  }

  object optNoSimplifications extends FlagOptionDef("nosimplifications", false)

  class SimplificationOptions(val simplify: Boolean)
  object SimplificationOptions {
    def apply(ctx: Context) =
      new SimplificationOptions(!ctx.options.findOptionOrDefault(optNoSimplifications))
  }

  /* XXX: We use an implicit conversion here instead of an implicit
   *      class in order for dependent types to work correctly. */
  implicit def factoryToTimeoutableFactory(sf: SolverFactory {
    type S <: TimeoutSolver
  }): TimeoutableFactory {
    val factory: sf.type
  } = new TimeoutableFactory {
    val factory: sf.type = sf
  }

  trait TimeoutableFactory { self =>
    val factory: SolverFactory { type S <: TimeoutSolver }

    def withTimeout(timeout: Long): TimeoutSolverFactory {
      val program: self.factory.program.type
      type S = self.factory.S { val program: self.factory.program.type }
    } = {
      val innerFactory = (factory match {
        case tsf: TimeoutSolverFactory => tsf.factory
        case _ => factory
      }).asInstanceOf[SolverFactory {
        val program: self.factory.program.type
        type S = self.factory.S { val program: self.factory.program.type }
      }]

      new TimeoutSolverFactory {
        val program: self.factory.program.type = innerFactory.program
        type S = self.factory.S { val program: self.factory.program.type }
        val to = timeout
        val factory = innerFactory
      }
    }

    def withTimeout(du: Duration): TimeoutSolverFactory {
      val program: self.factory.program.type
      type S = self.factory.S { val program: self.factory.program.type }
    } = withTimeout(du.toMillis)
  }
}
