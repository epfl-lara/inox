/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.parser.Commands.{Assert => SMTAssert, FunDef => SMTFunDef, _}
import _root_.smtlib.parser.Terms.{Identifier => _, _}
import _root_.smtlib.parser.CommandsResponses.{Error => ErrorResponse, _}

trait SMTLIBSolver extends Solver with SMTLIBTarget {

  import program._
  import trees._
  import symbols._
  import exprOps.variablesOf
  import SolverResponses._

  /* Solver name */
  def targetName: String
  override def name: String = "smt-"+targetName

  override def dbg(msg: => Any) = {
    debugOut foreach { o =>
      o.write(msg.toString)
      o.flush()
    }
  }

  /* Public solver interface */
  def assertCnstr(expr: Expr): Unit = if (!hasError) {
    try {
      variablesOf(expr).foreach(declareVariable)

      val term = toSMT(expr)(Map())
      emit(SMTAssert(term))
    } catch {
      case _ : SolverUnsupportedError =>
        // Store that there was an error. Now all following check()
        // invocations will return None
        addError()
    }
  }

  override def reset() = {
    emit(Reset(), rawOut = true) match {
      case ErrorResponse(msg) =>
        reporter.warning(s"Failed to reset $name: $msg")
        throw new CantResetException(this)
      case _ =>
    }
  }

  override def check(config: Configuration): config.Response[Model, Cores] = config.cast {
    if (hasError) Unknown else {
      emit(CheckSat()) match {
        case CheckSatStatus(SatStatus)     =>
          config match {
            case All | Model =>
              val syms = variables.aSet.map(variables.aToB)
              emit(GetModel()) match {
                case GetModelResponseSuccess(smodel) =>
                  // first-pass to gather functions
                  val modelFunDefs = smodel.collect {
                    case me @ DefineFun(SMTFunDef(a, args, _, _)) if args.nonEmpty =>
                      a -> me
                  }.toMap

                  val model = smodel.flatMap {
                    case DefineFun(SMTFunDef(s, _, _, e)) if syms(s) =>
                      try {
                        val v = variables.toA(s)
                        val value = fromSMT(e, v.getType)(Map(), modelFunDefs)
                        Some(v.toVal -> value)
                      } catch {
                        case _: Unsupported =>
                          None
                      }
                    case _ => None
                  }.toMap

                  SatWithModel(model)

                case _ =>
                  Unknown
              }
            case _ =>
              Sat
          }
        case CheckSatStatus(UnsatStatus) =>
          config match {
            case All | Cores =>
              emit(GetUnsatCore()) match {
                case GetUnsatCoreResponseSuccess(syms) =>
                  UnsatWithCores(Set.empty) // FIXME
                case _ =>
                  UnsatWithCores(Set.empty)
              }
            case _ =>
              Unsat
          }
        case CheckSatStatus(UnknownStatus) => Unknown
        case e                             => Unknown
      }
    }
  }

  def push(): Unit = {
    constructors.push()
    selectors.push()
    testers.push()
    variables.push()
    sorts.push()
    lambdas.push()
    functions.push()
    errors.push()

    emit(Push(1))
  }

  def pop(): Unit = {
    constructors.pop()
    selectors.pop()
    testers.pop()
    variables.pop()
    sorts.pop()
    lambdas.pop()
    functions.pop()
    errors.pop()

    emit(Pop(1))
  }

}
