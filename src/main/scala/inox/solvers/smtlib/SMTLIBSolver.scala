/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.trees.Terms.{Identifier => _, _}
import _root_.smtlib.trees.CommandsResponses._

import scala.collection.mutable.{Map => MutableMap}

abstract class SMTLIBSolver private(override val program: Program,
                                    override val context: inox.Context)
                                   (override val trees: program.trees.type,
                                    override val symbols: program.symbols.type,
                                    override val semantics: program.Semantics)
  extends AbstractSolver with SMTLIBTarget with SMTLIBDebugger {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}
  import exprOps.variablesOf
  import SolverResponses._

  def this(program: Program, context: inox.Context)(using semantics: program.Semantics) =
    this(program, context)(program.trees, program.symbols, semantics)

  override type Trees = Expr
  override type Model = program.Model

  /* Solver name */
  def targetName: String
  override def name: String = "smt-"+targetName

  override def dbg(msg: => Any) = {
    debugOut foreach { o =>
      o.write(msg.toString)
      o.flush()
    }
  }

  override def getSmtLibFileId: Option[Int] = this.getSmtLibFileIdIfDebug

  /* Public solver interface */
  def assertCnstr(expr: Expr): Unit = {
    variablesOf(expr).foreach(declareVariable)

    val term = toSMT(expr)(using Map())
    emit(Assert(term))
  }

  override def reset() = {
    emit(Reset(), rawOut = true) match {
      case Error(msg) =>
        reporter.warning(s"Failed to reset $name: $msg")
        throw new CantResetException(this)
      case _ =>
    }
  }

  protected def extractResponse(
    config: Configuration,
    res: SExpr,
    assumptions: Set[Expr]
  ): config.Response[Model, Assumptions] = config.cast(res match {
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

            val ctx = new Context(variables.bToA, Map(), modelFunDefs)

            val vars = smodel.flatMap {
              case DefineFun(SMTFunDef(s, args, _, e)) if syms(s) =>
                try {
                  val v = variables.toA(s)
                  val vargs = args.map(fromSMT(_)(using ctx).toVariable)
                  val value = fromSMT(e, v.getType)(using ctx.withVariables(args.map(_.name) zip vargs))
                  Some(v.toVal -> value) 
                } catch {
                  case _: Unsupported => None
                  case _: java.lang.StackOverflowError => None
                }
              case _ => None
            }.toMap

            val chooses: MutableMap[(Identifier, Seq[Type]), Expr] = MutableMap.empty
            chooses ++= ctx.getChooses.map(p => (p._1.res.id, Seq.empty[Type]) -> p._2)

            chooses ++= smodel.flatMap {
              case DefineFun(SMTFunDef(s, args, _, e)) if functions `containsB` s =>
                try {
                  val tfd = functions.toA(s)
                  tfd.fullBody match {
                    case Choose(res, _) =>
                      val ctx = new Context(variables.bToA, Map(), modelFunDefs).withVariables(args.map(_.name) zip tfd.params.map(_.toVariable))
                      val body = fromSMT(e, tfd.getType)(using ctx)
                      chooses ++= ctx.getChooses.map(p => (p._1.res.id, tfd.tps) -> p._2)
                      Some((res.id, tfd.tps) -> body)
                    case _ => None
                  }
                } catch {
                  case _: Unsupported => None
                  case _: java.lang.StackOverflowError => None
                }
              case _ => None
            }.toMap

            SatWithModel(inox.Model(program)(vars, chooses.toMap))

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
            UnsatWithAssumptions(syms.flatMap { lit =>
              variables.getA(lit.symbol).flatMap { v =>
                if (assumptions(v)) Some(v)
                else if (assumptions(Not(v))) Some(Not(v))
                else None
              }
            }.toSet)
          case _ =>
            UnsatWithAssumptions(Set.empty)
        }
      } else {
        Unsat
      }
    case CheckSatStatus(UnknownStatus) => Unknown
    case e                             => Unknown
  })

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    extractResponse(config, emit(CheckSat()), Set())

  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
    val props = assumptions.toSeq.map {
      case Not(v: Variable) => PropLiteral(declareVariable(v), false)
      case v: Variable => PropLiteral(declareVariable(v), true)
      case t => unsupported(t, "Assumptions must be either variables or their negation")
    }

    extractResponse(config, emit(CheckSatAssuming(props)), assumptions)
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
