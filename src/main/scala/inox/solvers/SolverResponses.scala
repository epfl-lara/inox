/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import scala.language.higherKinds
import scala.language.implicitConversions

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

  sealed trait Configuration {
    type Response[+M,+C] <: SolverResponse[M,C]
    def withModel: Boolean
    def withCores: Boolean

    def max(that: Configuration): Configuration = (this, that) match {
      case (All  , _    ) => All
      case (_    , All  ) => All
      case (Model, Cores) => All
      case (Cores, Model) => All
      case (Model, _    ) => Model
      case (_    , Model) => Model
      case (Cores, _    ) => Cores
      case (_    , Cores) => Cores
      case _              => Simple
    }

    def min(that: Configuration): Configuration = (this, that) match {
      case (o1, o2) if o1 == o2 => o1
      case (Simple, _) => Simple
      case (_, Simple) => Simple
      case (Model, Cores) => Simple
      case (Cores, Model) => Simple
      case (All, o) => o
      case (o, All) => o
    }

    def cast[M, C](resp: SolverResponse[M,C]): Response[M,C] = ((this, resp) match {
      case (_, Unknown)                            => Unknown
      case (Simple | Cores, Sat)                   => Sat
      case (Model  | All  , s @ SatWithModel(_))   => s
      case (Simple | Model, Unsat)                 => Unsat
      case (Cores  | All  , u @ UnsatWithCores(_)) => u
      case _ => throw FatalError("Unexpected response " + resp + " for configuration " + this)
    }).asInstanceOf[Response[M,C]]

    def convert[M1,C1,M2,C2](resp: Response[M1,C1], cm: M1 => M2, cc: C1 => C2): Response[M2,C2] =
      cast(resp.asInstanceOf[SolverResponse[M1,C1]] match {
        case Unknown               => Unknown
        case Sat                   => Sat
        case Unsat                 => Unsat
        case SatWithModel(model)   => SatWithModel(cm(model))
        case UnsatWithCores(cores) => UnsatWithCores(cc(cores))
      })
  }

  object Configuration {
    def apply(model: Boolean = false, cores: Boolean = false): Configuration =
      if (model && cores) All
      else if (model) Model
      else if (cores) Cores
      else Simple
  }

  case object Simple extends Configuration {
    type Response[+M,+C] = SimpleResponse
    def withModel = false
    def withCores = false
  }

  case object Model extends Configuration {
    type Response[+M,+C] = ResponseWithModel[M]
    def withModel = true
    def withCores = false
  }

  case object Cores extends Configuration {
    type Response[+M,+C] = ResponseWithCores[C]
    def withModel = false
    def withCores = true
  }

  case object All extends Configuration {
    type Response[+M,+C] = ResponseWithModelAndCores[M, C]
    def withModel = true
    def withCores = true
  }

  implicit def wideningConfiguration[M,C](config: Configuration)
                                         (resp: config.Response[M,C]): SolverResponse[M, C] = {
    resp.asInstanceOf[SolverResponse[M, C]]
  }
}

