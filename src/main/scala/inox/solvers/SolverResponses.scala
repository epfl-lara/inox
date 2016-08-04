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

  sealed trait Configuration[+Model, +Cores] {
    type Response <: SolverResponse[Model, Cores]

    def max[M >: Model,C >: Cores](that: Configuration[M, C]): Configuration[M, C] = (this, that) match {
      case (All()  , _      ) => All()
      case (_      , All()  ) => All()
      case (Model(), Cores()) => All()
      case (Cores(), Model()) => All()
      case (Model(), _      ) => Model()
      case (_      , Model()) => Model()
      case (Cores(), _      ) => Cores()
      case (_      , Cores()) => Cores()
      case _                  => Simple
    }

    def min[M >: Model, C >: Cores](that: Configuration[M, C]): Configuration[M, C] = (this, that) match {
      case (o1, o2) if o1 == o2 => o1
      case (Simple, _) => Simple
      case (_, Simple) => Simple
      case (Model(), Cores()) => Simple
      case (Cores(), Model()) => Simple
      case (All(), o) => o
      case (o, All()) => o
    }

    def cast[M <: Model, C <: Cores](resp: SolverResponse[M, C]): Response = ((this, resp) match {
      case (_, Unknown)                               => Unknown
      case (Simple  | Cores(), Sat)                   => Sat
      case (Model() | All()  , s @ SatWithModel(_))   => s
      case (Simple  | Model(), Unsat)                 => Unsat
      case (Cores() | All()  , u @ UnsatWithCores(_)) => u
      case _ => throw FatalError("Unexpected response " + resp + " for configuration " + this)
    }).asInstanceOf[Response]
  }

  object Configuration {
    def apply[M,C](model: Boolean = false, cores: Boolean = false): Configuration[M,C] =
      if (model && cores) All()
      else if (model) Model()
      else if (cores) Cores()
      else Simple
  }

  case object Simple extends Configuration[Nothing,Nothing] {
    type Response = SimpleResponse
  }

  case class Model[Model]() extends Configuration[Model,Nothing] {
    type Response = ResponseWithModel[Model]
  }

  case class Cores[Cores]() extends Configuration[Nothing,Cores] {
    type Response = ResponseWithCores[Cores]
  }

  case class All[Model,Cores]() extends Configuration[Model,Cores] {
    type Response = ResponseWithModelAndCores[Model, Cores]
  }
}

