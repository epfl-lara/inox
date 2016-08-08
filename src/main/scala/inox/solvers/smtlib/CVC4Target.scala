/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import org.apache.commons.lang3.StringEscapeUtils

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.Commands._
import _root_.smtlib.interpreters.CVC4Interpreter
import _root_.smtlib.theories.experimental.Sets
import _root_.smtlib.theories.experimental.Strings

trait CVC4Target extends SMTLIBTarget {
  import program._
  import trees._
  import symbols._

  def targetName = "cvc4"

  override def getNewInterpreter(ctx: InoxContext) = {
    val opts = interpreterOps(ctx)
    ctx.reporter.debug("Invoking solver with "+opts.mkString(" "))

    new CVC4Interpreter("cvc4", opts.toArray)
  }

  override protected def declareSort(t: Type): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case SetType(base) =>
          Sets.SetSort(declareSort(base))
        case StringType  => Strings.StringSort()
        case _ =>
          super.declareSort(t)
      }
    }
  }

  override protected def fromSMT(t: Term, otpe: Option[Type] = None)
                                (implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    (t, otpe) match {
      // EK: This hack is necessary for sygus which does not strictly follow smt-lib for negative literals
      case (SimpleSymbol(SSymbol(v)), Some(IntegerType)) if v.startsWith("-") =>
        try {
          IntegerLiteral(v.toInt)
        } catch {
          case _: Throwable =>
            super.fromSMT(t, otpe)
        }

      case (QualifiedIdentifier(SMTIdentifier(SSymbol("emptyset"), Seq()), _), Some(SetType(base))) =>
        FiniteSet(Seq(), base)

      case (FunctionApplication(QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), _), Seq(elem)), Some(MapType(k, v))) =>
        FiniteMap(Seq(), fromSMT(elem, v), k)

      case (FunctionApplication(SimpleSymbol(SSymbol("__array_store_all__")), Seq(_, elem)), Some(MapType(k, v))) =>
        FiniteMap(Seq(), fromSMT(elem, v), k)

      case (FunctionApplication(SimpleSymbol(SSymbol("store")), Seq(arr, key, elem)), Some(MapType(kT, vT))) =>
        val FiniteMap(elems, default, _) = fromSMT(arr, otpe)
        val newKey = fromSMT(key, kT)
        val newV   = fromSMT(elem, vT)
        val newElems = elems.filterNot(_._1 == newKey) :+ (newKey -> newV)
        FiniteMap(newElems, default, kT)

      case (FunctionApplication(SimpleSymbol(SSymbol("singleton")), elems), Some(SetType(base))) =>
        FiniteSet(elems.map(fromSMT(_, base)), base)

      case (FunctionApplication(SimpleSymbol(SSymbol("insert")), elems), Some(SetType(base))) =>
        val selems = elems.init.map(fromSMT(_, base))
        val FiniteSet(se, _) = fromSMT(elems.last, otpe)
        FiniteSet(se ++ selems, base)

      case (FunctionApplication(SimpleSymbol(SSymbol("union")), elems), Some(SetType(base))) =>
        FiniteSet(elems.flatMap(fromSMT(_, otpe) match {
          case FiniteSet(elems, _) => elems
        }), base)

      case (SString(v), Some(StringType)) =>
        StringLiteral(StringEscapeUtils.unescapeJava(v))

      case (Strings.Length(a), Some(IntegerType)) =>
        val aa = fromSMT(a)
        StringLength(aa)

      case (Strings.Concat(a, b, c @ _*), _) =>
        val aa = fromSMT(a)
        val bb = fromSMT(b)
        (StringConcat(aa, bb) /: c.map(fromSMT(_))) {
          case (s, cc) => StringConcat(s, cc)
        }
      
      case (Strings.Substring(s, start, offset), _) =>
        val ss = fromSMT(s)
        val tt = fromSMT(start)
        val oo = fromSMT(offset)
        oo match {
          case Minus(otherEnd, `tt`) => SubString(ss, tt, otherEnd)
          case _ =>
            SubString(ss, tt, Plus(tt, oo))
        }
        
      case (Strings.At(a, b), _) => fromSMT(Strings.Substring(a, b, SNumeral(1)))

      case _ =>
        super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]) = e match {
    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems, _) =>
      if (elems.isEmpty) {
        Sets.EmptySet(declareSort(fs.getType))
      } else {
        val selems = elems.map(toSMT)

        val sgt = Sets.Singleton(selems.head)

        if (selems.size > 1) {
          Sets.Insert(selems.tail :+ sgt)
        } else {
          sgt
        }
      }

    case SubsetOf(ss, s)        => Sets.Subset(toSMT(ss), toSMT(s))
    case ElementOfSet(e, s)     => Sets.Member(toSMT(e), toSMT(s))
    case SetDifference(a, b)    => Sets.Setminus(toSMT(a), toSMT(b))
    case SetUnion(a, b)         => Sets.Union(toSMT(a), toSMT(b))
    case SetIntersection(a, b)  => Sets.Intersection(toSMT(a), toSMT(b))

    /** String operations */
    case StringLiteral(v) =>
      declareSort(StringType)
      Strings.StringLit(StringEscapeUtils.escapeJava(v))
    case StringLength(a) => Strings.Length(toSMT(a))
    case StringConcat(a, b) => Strings.Concat(toSMT(a), toSMT(b))
    case SubString(a, start, Plus(start2, length)) if start == start2  =>
      Strings.Substring(toSMT(a),toSMT(start),toSMT(length))
    case SubString(a, start, end) =>
      Strings.Substring(toSMT(a),toSMT(start),toSMT(Minus(end, start)))
    case _ =>
      super.toSMT(e)
  }
}
