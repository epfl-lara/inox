/* Copyright 2009-2018 EPFL, Lausanne */

package inox

import scala.language.implicitConversions
import scala.concurrent.duration._

package object solvers {
  import combinators._

  object optAssumeChecked extends FlagOptionDef("assume-checked", false)

  case class PurityOptions(assumeChecked: Boolean)

  object PurityOptions {
    def apply(ctx: Context) =
      new PurityOptions(ctx.options.findOptionOrDefault(optAssumeChecked))

    def assumeChecked = new PurityOptions(true)
    def unchecked = new PurityOptions(false)
  }

  object optNoSimplifications extends FlagOptionDef("no-simplifications", false)

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

      // The casts are sadly needed; the trick with local class overriding `program` does not seem to work due to needing to override other things
      new TimeoutSolverFactory(innerFactory.program, timeout, new { type S = innerFactory.S }, innerFactory.asInstanceOf)
        .asInstanceOf[TimeoutSolverFactory {
          val program: self.factory.program.type
          type S = self.factory.S { val program: self.factory.program.type }
        }]
    }

    def withTimeout(du: Duration): TimeoutSolverFactory {
      val program: self.factory.program.type
      type S = self.factory.S { val program: self.factory.program.type }
    } = withTimeout(du.toMillis)
  }
}
