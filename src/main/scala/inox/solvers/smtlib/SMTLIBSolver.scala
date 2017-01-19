/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.parser.Terms.{Identifier => _, _}
import _root_.smtlib.parser.CommandsResponses._

trait SMTLIBSolver extends Solver with SMTLIBTarget with SMTLIBDebugger {

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
  def assertCnstr(expr: Expr): Unit = {
    variablesOf(expr).foreach(declareVariable)

    val term = toSMT(expr)(Map())
    emit(Assert(term))
  }

  override def reset() = {
    adtManager.reset()
    constructors.clear()
    selectors.clear()
    testers.clear()
    variables.clear()
    sorts.clear()
    lambdas.clear()
    functions.clear()

    emit(Reset(), rawOut = true) match {
      case Error(msg) =>
        reporter.warning(s"Failed to reset $name: $msg")
        throw new CantResetException(this)
      case _ =>
    }
  }

  protected def extractResponse(config: Configuration, res: SExpr): config.Response[Model, Assumptions] = {
    config.cast(res match {
      case CheckSatStatus(SatStatus) =>
        if (config.withModel) {
          val syms = variables.bSet
          emit(GetModel()) match {
            case GetModelResponseSuccess(smodel) =>
              // first-pass to gather functions
              val modelFunDefs = smodel.collect {
                case me @ DefineFun(SMTFunDef(a, args, _, _)) if args.nonEmpty =>
                  a -> me
              }.toMap

              val vars = smodel.flatMap {
                case DefineFun(SMTFunDef(s, _, _, e)) if syms(s) =>
                  try {
                    val v = variables.toA(s)
                    val value = fromSMT(e, v.getType)(Context(variables.bToA, modelFunDefs))
                    Some(v.toVal -> value)
                  } catch {
                    case _: Unsupported => None
                    case _: java.lang.StackOverflowError => None
                  }
                case _ => None
              }.toMap

              val chooses = smodel.flatMap {
                case DefineFun(SMTFunDef(s, args, _, e)) if functions containsB s =>
                  try {
                    val tfd = functions.toA(s)
                    tfd.fullBody match {
                      case Choose(res, _) =>
                        val ctx = Context(variables.bToA, modelFunDefs).withVariables(args.map(_.name) zip tfd.params.map(_.toVariable))
                        val body = fromSMT(e, tfd.returnType)(ctx)
                        Some((res.id, tfd.tps) -> body)
                      case _ => None
                    }
                  } catch {
                    case _: Unsupported => None
                    case _: java.lang.StackOverflowError => None
                  }
                case _ => None
              }.toMap

              SatWithModel(inox.Model(program)(vars, chooses))

            case _ =>
              Unknown
          }
        } else {
          Sat
        }
      case CheckSatStatus(UnsatStatus) =>
        if (config.withUnsatAssumptions) {
          emit(GetUnsatAssumptions()) match {
            case GetUnsatAssumptionsResponseSuccess(syms) =>
              UnsatWithAssumptions(syms.flatMap(s => variables.getA(s)).toSet)
            case _ =>
              UnsatWithAssumptions(Set.empty)
          }
        } else {
          Unsat
        }
      case CheckSatStatus(UnknownStatus) => Unknown
      case e                             => Unknown
    })
  }

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    extractResponse(config, emit(CheckSat()))

  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
    val props = assumptions.toSeq.map {
      case Not(v: Variable) => PropLiteral(variables.toB(v), false)
      case v: Variable => PropLiteral(variables.toB(v), true)
      case t => unsupported(t, "Assumptions must be either variables or their negation")
    }

    extractResponse(config, emit(CheckSatAssuming(props)))
  }

  def push(): Unit = {
    adtManager.push()
    constructors.push()
    selectors.push()
    testers.push()
    variables.push()
    sorts.push()
    lambdas.push()
    functions.push()

    emit(Push(1))
  }

  def pop(): Unit = {
    adtManager.pop()
    constructors.pop()
    selectors.pop()
    testers.pop()
    variables.pop()
    sorts.pop()
    lambdas.pop()
    functions.pop()

    emit(Pop(1))
  }

}
