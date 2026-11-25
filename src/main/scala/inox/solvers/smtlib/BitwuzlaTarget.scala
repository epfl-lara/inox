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


  // Bitwuzla has no integers, so the values of functions are 64-bit vectors instead. A model
  // numbers its closures from 0, so 2^64 closures are more than any query can tell apart. The
  // vectors are signed, like the literals of a model whose type isn't known.
  override protected def closureType: Type = BVType(true, 64)

  override protected def computeSort(t: Type): Sort = t match {
    case _ : BooleanType | _ : BVType | _ : CharType | _ : FPType | RoundingMode | _ : FunctionType | _ : MapType => super.computeSort(t)
    case UnitType() =>
      emit(DeclareSort(SSymbol("UnitType"), 0))
      Sort(SMTIdentifier(SSymbol("UnitType")))
    case other =>
      unsupported(other, s"Could not transform $other into an SMT sort")
  }

  override protected val interpreter: ProcessInterpreter = {
    val opts = interpreterOpts
    reporter.debug("Invoking solver with " + opts.mkString(" "))
    new PipelinedBitwuzlaInterpreter("bitwuzla", opts.toArray)
  }

  override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]): Term = e match {
    case UnitLiteral() =>
      declareSort(UnitType())
      declareVariable(Variable.fresh("Unit", UnitType()))
    case _ => super.toSMT(e)
  }

  // Bitwuzla gives the value of a map as stores over a constant array, which are the updates of a
  // finite map: the model's values must be finite maps themselves
  override protected def fromSMT(t: Term, otpe: Option[Type] = None)(using Context): Expr = (t, otpe) match {
    case (ArraysEx.Store(arr, key, value), Some(mt @ MapType(from, to))) =>
      fromSMT(arr, mt) match {
        case FiniteMap(elems, default, _, _) =>
          val k = fromSMT(key, from)
          FiniteMap(elems.filter(_._1 != k) :+ (k -> fromSMT(value, to)), default, from, to)
        case _ => super.fromSMT(t, otpe)
      }
    case _ => super.fromSMT(t, otpe)
  }

}
