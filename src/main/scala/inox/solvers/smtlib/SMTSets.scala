/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{Term, Sort}
import _root_.smtlib.theories.cvc.Sets

trait SMTSets extends SMTLIBTarget with SMTLIBDebugger {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  protected val setTarget: Sets
  import setTarget._

  override protected def computeSort(t: Type): Sort = t match {
    case SetType(base) => SetSort(declareSort(base))
    case _ => super.computeSort(t)
  }

  override protected def fromSMT(t: Term, otpe: Option[Type] = None)(using Context): Expr = {
    (t, otpe) match {
      case (EmptySet(sort), Some(SetType(base))) => FiniteSet(Seq.empty, base)
      case (EmptySet(sort), _) => FiniteSet(Seq.empty, fromSMT(sort))

      case (Singleton(e), Some(SetType(base))) => FiniteSet(Seq(fromSMT(e, base)), base)
      case (Singleton(e), _) =>
        val elem = fromSMT(e)
        FiniteSet(Seq(elem), elem.getType)

      case (Insert(set, es@_*), Some(SetType(base))) => es.foldLeft(fromSMT(set, SetType(base))) {
        case (FiniteSet(elems, base), e) =>
          val elem = fromSMT(e, base)
          FiniteSet(elems.filter(_ != elem) :+ elem, base)
        case (s, e) => SetAdd(s, fromSMT(e, base))
      }

      case (Insert(set, es@_*), _) => es.foldLeft(fromSMT(set)) {
        case (FiniteSet(elems, base), e) =>
          val elem = fromSMT(e, base)
          FiniteSet(elems.filter(_ != elem) :+ elem, base)
        case (s, e) => SetAdd(s, fromSMT(e))
      }

      case (Union(e1, e2), Some(SetType(base))) =>
        (fromSMT(e1, SetType(base)), fromSMT(e2, SetType(base))) match {
          case (FiniteSet(elems1, _), FiniteSet(elems2, _)) => FiniteSet(elems1 ++ elems2, base)
          case (s1, s2) => SetUnion(s1, s2)
        }

      case (Union(e1, e2), _) =>
        (fromSMT(e1), fromSMT(e2)) match {
          case (fs1@FiniteSet(elems1, b1), fs2@FiniteSet(elems2, b2)) =>
            val tpe = leastUpperBound(b1, b2)
            if (tpe == Untyped) unsupported(SetUnion(fs1, fs2), "woot? incompatible set base-types")
            FiniteSet(elems1 ++ elems2, tpe)
          case (s1, s2) => SetUnion(s1, s2)
        }

      case _ => super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(using bindings: Map[Identifier, Term]) = e match {
    case fs@FiniteSet(elems, _) =>
      if (elems.isEmpty) {
        EmptySet(declareSort(fs.getType))
      } else {
        val selems = elems.map(toSMT)

        if (exprOps.variablesOf(elems.head).isEmpty) {
          val sgt = Singleton(selems.head)

          if (selems.size > 1) {
            Insert(selems.tail :+ sgt)
          } else {
            sgt
          }
        } else {
          val sgt = EmptySet(declareSort(fs.getType))
          Insert(selems :+ sgt)
        }
      }
    case SubsetOf(ss, s) => Subset(toSMT(ss), toSMT(s))
    case ElementOfSet(e, s) => Member(toSMT(e), toSMT(s))
    case SetDifference(a, b) => Setminus(toSMT(a), toSMT(b))
    case SetUnion(a, b) => Union(toSMT(a), toSMT(b))
    case SetAdd(a, b) => Insert(toSMT(b), toSMT(a))
    case SetIntersection(a, b) => Intersection(toSMT(a), toSMT(b))

    case _ =>
      super.toSMT(e)
  }
}
