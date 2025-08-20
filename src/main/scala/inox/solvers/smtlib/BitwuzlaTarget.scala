package inox
package solvers
package smtlib

import _root_.smtlib.trees.Commands.*
import _root_.smtlib.interpreters.*
import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.trees.Commands._
import _root_.smtlib.theories._

trait BitwuzlaTarget extends SMTLIBTarget with SMTLIBDebugger {

  import context.{*, given}
  import program._
  import program.trees._
  import program.symbols.{given, _}


  def targetName = "bitwuzla"


  override protected def computeSort(t: Type): Sort = t match {
    case _ : BooleanType | _ : BVType | _ : FPType | RoundingMode | _ : FunctionType => super.computeSort(t)
    case UnitType() =>
      emit(DeclareSort(SSymbol("UnitType"), 0))
      Sort(SMTIdentifier(SSymbol("UnitType")))
    case other =>
      unsupported(other, s"Could not transform $other into an SMT sort")
  }

  override protected val interpreter: ProcessInterpreter = {
    val opts = interpreterOpts
    reporter.debug("Invoking solver with " + opts.mkString(" "))
    new BitwuzlaInterpreter("bitwuzla", opts.toArray)
  }

  override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]): Term = e match {
    case UnitLiteral() =>
      declareSort(UnitType())
      declareVariable(Variable.fresh("Unit", UnitType()))
    case _ => super.toSMT(e)
  }

//  override protected def fromSMT(t: Term, otpe: Option[Type] = None)(using Context): Expr = {
//    (t, otpe) match {
//      case (_, Some(UnitType())) =>
//        UnitLiteral()
//      case _ => super.fromSMT(t, otpe)
//    }
//  }

}
