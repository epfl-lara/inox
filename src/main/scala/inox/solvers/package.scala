/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import scala.language.implicitConversions
import scala.concurrent.duration._

package object solvers {
  import combinators._

  /* XXX: We use an implicit conversion here instead of an implicit
   *      class in order for dependent types to work correctly. */
  implicit def factoryToTimeoutableFactory(sf: SolverFactory {
    type S <: TimeoutSolver
  }): TimeoutableFactory {
    val factory: sf.type
    type S = sf.S { val program: sf.program.type }
  } = new TimeoutableFactory {
    val factory: sf.type = sf
    type S = sf.S { val program:sf.program.type }
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

    def withTimeout(optTimeout: Option[Long]): SolverFactory {
      val program: self.factory.program.type
      type S = self.factory.S { val program: self.factory.program.type }
    } = optTimeout match {
      case Some(to) =>
        withTimeout(to)

      case None =>
        // XXX @nv: stupid type checker...
        factory.asInstanceOf[SolverFactory {
          val program: self.factory.program.type
          type S = self.factory.S { val program: self.factory.program.type }
        }]
    }
  }

}
