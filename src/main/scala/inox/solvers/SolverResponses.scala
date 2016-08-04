/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

object SolverResponses {
  sealed trait SolverResponse[+Model,+Cores]

  sealed trait Satisfiable
  sealed trait Unsatisfiable

  sealed trait SimpleResponse extends SolverResponse[Nothing, Nothing]
  sealed trait ResponseWithModel[+Model] extends SolverResponse[Model, Nothing]
  sealed trait ResponseWithCores[+Cores] extends SolverResponse[Nothing, Cores]
  sealed trait ResponseWithModelAndCores[+Model,+Cores] extends SolverResponse[Model, Cores]

  case object Sat extends Satisfiable
    with SimpleResponse
    with ResponseWithCores[Nothing]

  case object Unsat extends Unsatisfiable
    with SimpleResponse
    with ResponseWithModel[Nothing]

  case class SatWithModel[Model](model: Model) extends Satisfiable
    with ResponseWithModel[Model]
    with ResponseWithModelAndCores[Model, Nothing]

  case class UnsatWithCores[Cores](cores: Cores) extends Unsatisfiable
    with ResponseWithCores[Cores]
    with ResponseWithModelAndCores[Nothing, Cores]

  case object Unknown extends SimpleResponse
    with ResponseWithModel[Nothing]
    with ResponseWithCores[Nothing]
    with ResponseWithModelAndCores[Nothing, Nothing]

  object Check {
    def unapply[Core,Model](resp: SolverResponse[Core,Model]): Option[Boolean] = resp match {
      case _: Satisfiable   => Some(true)
      case _: Unsatisfiable => Some(false)
      case Unknown => None
    }
  }
}

