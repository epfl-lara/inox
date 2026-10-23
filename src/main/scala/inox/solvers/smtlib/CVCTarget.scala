/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.trees.Commands._
import _root_.smtlib.theories._
import _root_.smtlib.theories.cvc._

trait CVCTarget extends SMTLIBTarget with SMTSets with SMTLIBDebugger {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  override protected def fromSMT(t: Term, otpe: Option[Type] = None)(using Context): Expr = {
    (t, otpe) match {
      // EK: This hack is necessary for sygus which does not strictly follow smt-lib for negative literals
      case (SimpleSymbol(SSymbol(v)), Some(IntegerType())) if v.startsWith("-") =>
        try {
          IntegerLiteral(v.toInt)
        } catch {
          case _: Throwable => super.fromSMT(t, otpe)
        }

      // XXX @nv: CVC4 seems to return some weird representations for certain adt selectors
      case (FunctionApplication(SimpleSymbol(s), Seq(e)), _)
      if s.name.endsWith("'") && selectors.containsB(SSymbol(s.name.init)) =>
        fromSMT(FunctionApplication(SimpleSymbol(SSymbol(s.name.init)), Seq(e)), otpe)

      // XXX @nv: CVC4 seems to return some weird representations for certain adt constructors
      case (FunctionApplication(SimpleSymbol(s), args), _)
      if s.name.endsWith("'") && constructors.containsB(SSymbol(s.name.init)) =>
        fromSMT(FunctionApplication(SimpleSymbol(SSymbol(s.name.init)), args), otpe)

      // XXX @nv: CVC4 seems to return bv literals instead of booleans sometimes
      case (FixedSizeBitVectors.BitVectorLit(bs), Some(BooleanType())) if bs.size == 1 =>
        BooleanLiteral(bs.head)
      case (FixedSizeBitVectors.BitVectorConstant(n, size), Some(BooleanType())) if size == 1 =>
        BooleanLiteral(n == 1)
      case (Core.Equals(e1, e2), _) =>
        fromSMTUnifyType(e1, e2, None)(Equals.apply) match {
          case Equals(IsTyped(lhs, BooleanType()), IsTyped(_, BVType(true, 1))) =>
            Equals(lhs, fromSMT(e2, BooleanType()))
          case Equals(IsTyped(_, BVType(true, 1)), IsTyped(rhs, BooleanType())) =>
            Equals(fromSMT(e1, BooleanType()), rhs)
          case expr => expr
        }

      case (ArraysEx.Store(e1, e2, e3), Some(MapType(from, to))) =>
        (fromSMT(e1, MapType(from, to)), fromSMT(e2, from), fromSMT(e3, to)) match {
          case (FiniteMap(elems, default, _, _), key, value) => FiniteMap(elems :+ (key -> value), default, from, to)
          case _ => super.fromSMT(t, otpe)
        }

      case (ArraysEx.Store(e1, e2, e3), _) =>
        (fromSMT(e1), fromSMT(e2), fromSMT(e3)) match {
          case (FiniteMap(elems, default, from, to), key, value) => FiniteMap(elems :+ (key -> value), default, from, to)
          case _ => super.fromSMT(t, otpe)
        }

      case (FunctionApplication(SimpleSymbol(SSymbol("__array_store_all__")), Seq(_, elem)), Some(MapType(k, v))) =>
        FiniteMap(Seq(), fromSMT(elem, v), k, v)

      case _ => super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]) = e match {
    case FiniteMap(_, default, _, _) if !isValue(default) || exprOps.exists {
      case _: Lambda => true
      case _ => false
    } (default) =>
      unsupported(e, "Cannot encode map with non-constant default value")

    case _ =>
      super.toSMT(e)
  }
}
