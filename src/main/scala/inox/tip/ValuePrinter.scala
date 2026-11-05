/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package tip

import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, Let => SMTLet, _}
import _root_.smtlib.theories._
import _root_.smtlib.theories.cvc.{CVC4Sets => Sets}
import _root_.smtlib.extensions.tip.Terms.{Lambda => SMTLambda}
import _root_.smtlib.printer.RecursivePrinter

/** Prints model values as SMT-LIB terms, for tools that drive Inox
  * through its command line (see `--model-format=smtlib`).
  *
  * The output uses the syntax that Inox's TIP parser reads, so a printed
  * value can be parsed back in the context of the problem it answers:
  *  - integers, reals, booleans, bit-vectors (`#b...`, characters as 16-bit
  *    vectors) and strings (with the SMT-LIB `\u{...}` escapes);
  *  - datatype values, with nullary constructors of parametric datatypes
  *    qualified by their sort, as in `(as nil (list Int))`. Values of a
  *    `declare-sort` sort are printed as Inox encodes them, `(S n)` for the
  *    n-th value of sort `S`;
  *  - maps as arrays, `(store ((as const (Array K V)) d) k v)`;
  *  - sets and bags in the CVC4 syntax that Inox's TIP printer and parser
  *    use, e.g. `(insert (as emptyset Int) 1 2)`; they are not part of the
  *    SMT-LIB standard;
  *  - functions as `lambda` terms over `ite`, `=`, `and`, `or`, `not` and
  *    `let`, and abstract values of type parameters as `@T_n`.
  *
  * Free variables, sorts and constructors are printed with the names they
  * had in the input, so a TIP producer can map a model back to its own
  * terms. Variables bound inside values (lambda parameters) get unique names.
  */
object ValuePrinter {
  import inox.trees._

  case class UnsupportedValue(desc: String) extends Exception(s"cannot print $desc as SMT-LIB")

  private def symbol(name: String): SSymbol = SSymbol(name)
  private def simple(name: String): QualifiedIdentifier = QualifiedIdentifier(SimpleIdentifier(symbol(name)))

  private def bits(size: Int, isSet: Int => Boolean): Term =
    FixedSizeBitVectors.BitVectorLit((size to 1 by -1).map(isSet).toList)

  private def integer(n: BigInt): Term =
    if (n < 0) Ints.Neg(SNumeral(-n)) else SNumeral(n)

  def toSort(tpe: Type)(using Symbols): Sort = tpe match {
    case IntegerType() => Ints.IntSort()
    case BooleanType() => Core.BoolSort()
    case RealType() => Reals.RealSort()
    case BVType(_, size) => FixedSizeBitVectors.BitVectorSort(size)
    case CharType() => FixedSizeBitVectors.BitVectorSort(16)
    case StringType() => Strings.StringSort()
    case adt: ADTType => Sort(SimpleIdentifier(symbol(adt.id.name)), adt.tps.map(toSort))
    case TypeParameter(id, _) => Sort(SimpleIdentifier(symbol(id.name)))
    case FunctionType(from, to) => Sort(SimpleIdentifier(symbol("=>")), (from :+ to).map(toSort))
    case MapType(from, to) => ArraysEx.ArraySort(toSort(from), toSort(to))
    case SetType(base) => Sets.SetSort(toSort(base))
    case BagType(base) => Bags.BagSort(toSort(base))
    case _ => throw UnsupportedValue(tpe.toString)
  }

  def toTerm(e: Expr)(using s: Symbols): Term = e match {
    case IntegerLiteral(v) => integer(v)
    case BooleanLiteral(b) => if (b) Core.True() else Core.False()
    case FractionLiteral(n, d) => Reals.Div(integer(n), SNumeral(d))
    case UMinus(a) => Ints.Neg(toTerm(a))
    case BVLiteral(_, value, size) => bits(size, value)
    case CharLiteral(c) => bits(16, i => (c.toInt >> (i - 1) & 1) == 1)
    case StringLiteral(v) => Strings.StringLit(utils.StringUtils.encode(v))

    case ADT(id, tps, Seq()) =>
      val cons = s.getConstructor(id)
      if (cons.getSort.tparams.isEmpty) simple(id.name)
      else QualifiedIdentifier(SimpleIdentifier(symbol(id.name)), Some(toSort(ADTType(cons.sort, tps))))
    case ADT(id, _, args) => FunctionApplication(simple(id.name), args.map(toTerm))
    case GenericValue(tp, n) => simple(s"@${tp.id.name}_$n")

    case FiniteMap(pairs, default, from, to) =>
      val const = FunctionApplication(
        QualifiedIdentifier(SimpleIdentifier(symbol("const")), Some(ArraysEx.ArraySort(toSort(from), toSort(to)))),
        Seq(toTerm(default)))
      pairs.foldLeft(const: Term) { case (m, (k, v)) => ArraysEx.Store(m, toTerm(k), toTerm(v)) }
    case FiniteSet(elems, base) =>
      val empty = Sets.EmptySet(toSort(base))
      elems.map(toTerm) match {
        case x +: xs => Sets.Insert(empty, x, xs*)
        case _ => empty
      }
    case FiniteBag(elems, base) =>
      elems.foldLeft(Bags.EmptyBag(toSort(base))) { case (b, (k, v)) =>
        Bags.Union(b, Bags.Singleton(toTerm(k), toTerm(v)))
      }

    case v: Variable => simple(v.id.uniqueName)
    case Lambda(params, body) =>
      val vars = params.map(vd => SortedVar(symbol(vd.id.uniqueName), toSort(vd.getType)))
      SMTLambda(vars, toTerm(body))
    case IfExpr(c, t, f) => Core.ITE(toTerm(c), toTerm(t), toTerm(f))
    case Equals(a, b) => Core.Equals(toTerm(a), toTerm(b))
    case And(es) => Core.And(es.map(toTerm))
    case Or(es) => Core.Or(es.map(toTerm))
    case Not(a) => Core.Not(toTerm(a))
    case Let(vd, v, b) => SMTLet(VarBinding(symbol(vd.id.uniqueName), toTerm(v)), Seq(), toTerm(b))
    case _ => throw UnsupportedValue(e.toString)
  }

  def sort(tpe: Type)(using Symbols): String = RecursivePrinter.toString(toSort(tpe))

  def value(e: Expr)(using Symbols): String = RecursivePrinter.toString(toTerm(e))

  /** The model in `get-value` response form: `((x v) (y w) ...)`. */
  def model(vars: Map[ValDef, Expr])(using Symbols): String =
    vars.toSeq.sortBy(_._1.id.name).map { case (vd, v) => s"(${vd.id.name} ${value(v)})" }
      .mkString("(", " ", ")")
}
