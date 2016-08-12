/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers

import scala.language.higherKinds
import scala.language.implicitConversions

object SolverResponses {
  sealed trait SolverResponse[+Model,+Assumptions] {
    def isSAT: Boolean
    def isUNSAT: Boolean
  }

  sealed trait Satisfiable {
    def isSAT: Boolean = true
    def isUNSAT: Boolean = false
  }

  sealed trait Unsatisfiable {
    def isSAT: Boolean = false
    def isUNSAT: Boolean = true
  }

  sealed trait CheckResponse

  sealed trait SimpleResponse extends SolverResponse[Nothing, Nothing] with CheckResponse
  sealed trait ResponseWithModel[+Model] extends SolverResponse[Model, Nothing] with CheckResponse
  sealed trait ResponseWithUnsatAssumptions[+Assumptions] extends SolverResponse[Nothing, Assumptions]
  sealed trait ResponseWithModelAndAssumptions[+Model,+Assumptions] extends SolverResponse[Model, Assumptions]

  case object Sat extends Satisfiable
    with SimpleResponse
    with ResponseWithUnsatAssumptions[Nothing]

  case object Unsat extends Unsatisfiable
    with SimpleResponse
    with ResponseWithModel[Nothing]

  case class SatWithModel[Model](model: Model) extends Satisfiable
    with ResponseWithModel[Model]
    with ResponseWithModelAndAssumptions[Model, Nothing]

  case class UnsatWithAssumptions[Trees](assumptions: Set[Trees]) extends Unsatisfiable
    with ResponseWithUnsatAssumptions[Set[Trees]]
    with ResponseWithModelAndAssumptions[Nothing, Set[Trees]]

  case object Unknown extends SimpleResponse
    with ResponseWithModel[Nothing]
    with ResponseWithUnsatAssumptions[Nothing]
    with ResponseWithModelAndAssumptions[Nothing, Nothing] {
      def isSAT: Boolean = false
      def isUNSAT: Boolean = false
    }

  object Check {
    def unapply[Model,Assumptions](resp: SolverResponse[Model,Assumptions]): Option[Boolean] = resp match {
      case _: Satisfiable   => Some(true)
      case _: Unsatisfiable => Some(false)
      case Unknown => None
    }
  }

  sealed trait Configuration {
    type Response[+M,+C] <: SolverResponse[M,C]
    def withModel: Boolean
    def withUnsatAssumptions: Boolean

    def max(that: Configuration): Configuration = (this, that) match {
      case (All  , _    ) => All
      case (_    , All  ) => All
      case (Model, UnsatAssumptions) => All
      case (UnsatAssumptions, Model) => All
      case (Model, _    ) => Model
      case (_    , Model) => Model
      case (UnsatAssumptions, _    ) => UnsatAssumptions
      case (_    , UnsatAssumptions) => UnsatAssumptions
      case _              => Simple
    }

    def min(that: Configuration): Configuration = (this, that) match {
      case (o1, o2) if o1 == o2 => o1
      case (Simple, _) => Simple
      case (_, Simple) => Simple
      case (Model, UnsatAssumptions) => Simple
      case (UnsatAssumptions, Model) => Simple
      case (All, o) => o
      case (o, All) => o
    }

    def cast[M, C](resp: SolverResponse[M,C]): Response[M,C] = ((this, resp) match {
      case (_, Unknown) => Unknown
      case (Simple | UnsatAssumptions, Sat) => Sat
      case (Model  | All, s @ SatWithModel(_)) => s
      case (Simple | Model, Unsat) => Unsat
      case (UnsatAssumptions | All, u @ UnsatWithAssumptions(_)) => u
      case _ => throw FatalError("Unexpected response " + resp + " for configuration " + this)
    }).asInstanceOf[Response[M,C]]

    def convert[M1,T1,M2,T2](resp: Response[M1,Set[T1]], cm: M1 => M2, cc: Set[T1] => Set[T2]): Response[M2,Set[T2]] =
      cast(resp.asInstanceOf[SolverResponse[M1,Set[T1]]] match {
        case Unknown               => Unknown
        case Sat                   => Sat
        case Unsat                 => Unsat
        case SatWithModel(model)   => SatWithModel(cm(model))
        case UnsatWithAssumptions(cores) => UnsatWithAssumptions(cc(cores))
      })
  }

  object Configuration {
    def apply(model: Boolean = false, unsatAssumptions: Boolean = false): Configuration =
      if (model && unsatAssumptions) All
      else if (model) Model
      else if (unsatAssumptions) UnsatAssumptions
      else Simple
  }

  sealed trait CheckConfiguration extends Configuration {
    type Response[+M,+C] <: SolverResponse[M,C] with CheckResponse

    override def withUnsatAssumptions = false

    override def min(that: Configuration): CheckConfiguration =
      super.min(that).asInstanceOf[CheckConfiguration]
  }

  case object Simple extends CheckConfiguration {
    type Response[+M,+C] = SimpleResponse
    def withModel = false
  }

  case object Model extends CheckConfiguration {
    type Response[+M,+C] = ResponseWithModel[M]
    def withModel = true
  }

  case object UnsatAssumptions extends Configuration {
    type Response[+M,+C] = ResponseWithUnsatAssumptions[C]
    def withModel = false
    def withUnsatAssumptions = true
  }

  case object All extends Configuration {
    type Response[+M,+C] = ResponseWithModelAndAssumptions[M, C]
    def withModel = true
    def withUnsatAssumptions = true
  }

  implicit def wideningConfiguration[M,C](config: Configuration)
                                         (resp: config.Response[M,C]): SolverResponse[M, C] = {
    resp.asInstanceOf[SolverResponse[M, C]]
  }
}

