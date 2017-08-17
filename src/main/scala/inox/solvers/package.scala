/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import scala.language.implicitConversions
import scala.concurrent.duration._

package object solvers {
  import combinators._

  object optAssumeChecked extends FlagOptionDef("assumechecked", false)
  object optTotalFunctions extends FlagOptionDef("totalfunctions", false)
  object optNoSimplifications extends FlagOptionDef("nosimplifications", false)

  class PurityOptions(val assumeChecked: Boolean, val totalFunctions: Boolean) {
    override def equals(that: Any): Boolean = (that != null) && (that match {
      case p: PurityOptions => assumeChecked == p.assumeChecked && totalFunctions == p.totalFunctions
      case _ => false
    })

    override def hashCode: Int = (if (assumeChecked) 2 else 0) + (if (totalFunctions) 1 else 0)
  }

  object PurityOptions {
    def apply(ctx: Context) = new PurityOptions(
      ctx.options.findOptionOrDefault(optAssumeChecked),
      ctx.options.findOptionOrDefault(optTotalFunctions))

    def apply(assumeChecked: Boolean = false, totalFunctions: Boolean = false) =
      new PurityOptions(assumeChecked, totalFunctions)
  }

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
