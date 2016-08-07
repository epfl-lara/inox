/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import scala.concurrent.duration._

package object solvers {
  import combinators._

  implicit class TimeoutableSolverFactory[S1 <: TimeoutSolver](val sf: SolverFactory { type S = S1 }) {
    def withTimeout(timeout: Long): TimeoutSolverFactory { type S <: S1 } = {
      val innerFactory = (sf match {
        case tsf: TimeoutSolverFactory => tsf.factory
        case _ => sf
      }).asInstanceOf[SolverFactory {
        val program: sf.program.type
        type S = S1 { val program: sf.program.type }
      }]

      new TimeoutSolverFactory {
        val program: sf.program.type = sf.program
        type S = S1 { val program: sf.program.type }
        val to = timeout
        val factory = innerFactory
      }
    }

    def withTimeout(du: Duration): TimeoutSolverFactory { type S <: S1 } = {
      withTimeout(du.toMillis)
    }
  }
}
