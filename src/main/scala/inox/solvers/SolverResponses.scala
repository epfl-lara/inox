/* Copyright 2009-2018 EPFL, Lausanne */

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
  sealed trait ResponseWithProof extends SolverResponse[Nothing, Nothing] with CheckResponse
  sealed trait ResponseWithModelAndProof[+Model] extends SolverResponse[Model, Nothing] with CheckResponse

  case object Sat extends Satisfiable
    with SimpleResponse
    with ResponseWithUnsatAssumptions[Nothing]
    with ResponseWithProof

  case object Unsat extends Unsatisfiable
    with SimpleResponse
    with ResponseWithModel[Nothing]

  /** An unsat answer with its proof, or why there is none (see [[Proof]]). */
  case class UnsatWithProof(proof: Either[String, certificates.Proof]) extends Unsatisfiable
    with ResponseWithProof
    with ResponseWithModelAndProof[Nothing]

  case class SatWithModel[Model](model: Model) extends Satisfiable
    with ResponseWithModel[Model]
    with ResponseWithModelAndAssumptions[Model, Nothing]
    with ResponseWithModelAndProof[Model]

  case class UnsatWithAssumptions[Trees](assumptions: Set[Trees]) extends Unsatisfiable
    with ResponseWithUnsatAssumptions[Set[Trees]]
    with ResponseWithModelAndAssumptions[Nothing, Set[Trees]]

  case object Unknown extends SimpleResponse
    with ResponseWithModel[Nothing]
    with ResponseWithUnsatAssumptions[Nothing]
    with ResponseWithModelAndAssumptions[Nothing, Nothing]
    with ResponseWithProof
    with ResponseWithModelAndProof[Nothing] {
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
    /** Whether an unsat answer comes with a proof, as with SMT-LIB's `:produce-proofs`: a solver
      * that produces proofs gives its proof, and the other solvers say that they don't. */
    def withProof: Boolean = false

    def max(that: Configuration): Configuration =
      Configuration(model = withModel || that.withModel, unsatAssumptions = withUnsatAssumptions || that.withUnsatAssumptions,
        proof = withProof || that.withProof)

    def min(that: Configuration): Configuration =
      Configuration(model = withModel && that.withModel, unsatAssumptions = withUnsatAssumptions && that.withUnsatAssumptions,
        proof = withProof && that.withProof)

    def cast[M, C](resp: SolverResponse[M,C]): Response[M,C] = ((this, resp) match {
      case (_, Unknown) => Unknown
      case (Simple | UnsatAssumptions | Proof, Sat) => Sat
      case (Model  | All | ModelAndProof, s @ SatWithModel(_)) => s
      case (Simple | Model, Unsat | UnsatWithProof(_)) => Unsat
      case (Proof | ModelAndProof, Unsat) => UnsatWithProof(Left("the solver does not produce proofs"))
      case (Proof | ModelAndProof, u @ UnsatWithProof(_)) => u
      case (UnsatAssumptions | All, u @ UnsatWithAssumptions(_)) => u
      case _ => throw FatalError("Unexpected response " + resp + " for configuration " + this)
    }).asInstanceOf[Response[M,C]]

    def convert[M1,T1,M2,T2](resp: Response[M1,Set[T1]], cm: M1 => M2, cc: Set[T1] => Set[T2]): Response[M2,Set[T2]] =
      cast(resp.asInstanceOf[SolverResponse[M1,Set[T1]]] match {
        case Unknown               => Unknown
        case Sat                   => Sat
        case Unsat                 => Unsat
        case u @ UnsatWithProof(_) => u
        case SatWithModel(model)   => SatWithModel(cm(model))
        case UnsatWithAssumptions(cores) => UnsatWithAssumptions(cc(cores))
      })
  }

  object Configuration {
    /** The configuration with these features, where there are no proofs with unsat assumptions. */
    def apply(model: Boolean = false, unsatAssumptions: Boolean = false, proof: Boolean = false): Configuration =
      if (proof && !unsatAssumptions) { if (model) ModelAndProof else Proof }
      else if (model && unsatAssumptions) All
      else if (model) Model
      else if (unsatAssumptions) UnsatAssumptions
      else Simple
  }

  sealed trait CheckConfiguration extends Configuration {
    type Response[+M,+C] <: SolverResponse[M,C] & CheckResponse

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

  /** Asks for the proof of an unsat answer, see [[Configuration.withProof]]. */
  case object Proof extends CheckConfiguration {
    type Response[+M,+C] = ResponseWithProof
    def withModel = false
    override def withProof = true
  }

  case object ModelAndProof extends CheckConfiguration {
    type Response[+M,+C] = ResponseWithModelAndProof[M]
    def withModel = true
    override def withProof = true
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

