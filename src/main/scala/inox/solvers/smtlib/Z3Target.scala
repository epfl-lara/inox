/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, Let => SMTLet, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.interpreters.Z3Interpreter
import _root_.smtlib.theories.Core.{Equals => SMTEquals, _}
import _root_.smtlib.theories._

trait Z3Target extends SMTLIBTarget with SMTLIBDebugger {
  import program._
  import trees._
  import symbols._

  def targetName = "z3"

  protected def interpreterOpts = Seq(
    "-in",
    "-smt2"
  )

  protected val interpreter = {
    val opts = interpreterOpts
    ctx.reporter.debug("Invoking solver "+targetName+" with "+opts.mkString(" "))
    new Z3Interpreter("z3", opts.toArray)
  }

  protected val extSym = SSymbol("_")

  protected lazy val setSort: SSymbol = {
    val s = SSymbol("Set")
    val t = SSymbol("T")

    val arraySort = Sort(
      SMTIdentifier(SSymbol("Array")),
      Seq(Sort(SMTIdentifier(t)), BoolSort())
    )

    val cmd = DefineSort(s, Seq(t), arraySort)
    emit(cmd)
    s
  }

  override protected def computeSort(t: Type): Sort = t match {
    case SetType(base) =>
      declareSort(BooleanType)
      Sort(SMTIdentifier(setSort), Seq(declareSort(base)))
    case BagType(base) => declareSort(MapType(base, IntegerType))
    case _ => super.computeSort(t)
  }

  override protected def fromSMT(t: Term, otpe: Option[Type] = None)
                                (implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
    (t, otpe) match {
      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe @ MapType(keyType, valueType))) =>
        if (letDefs contains k) {
          val DefineFun(SMTFunDef(a, Seq(SortedVar(arg, akind)), rkind, body)) = letDefs(k)

          def extractCases(e: Term): (Map[Expr, Expr], Expr) = e match {
            case ITE(SMTEquals(SimpleSymbol(`arg`), k), v, e) =>
              val (cs, d) = extractCases(e)
              (Map(fromSMT(k, keyType) -> fromSMT(v, valueType)) ++ cs, d)
            case e =>
              (Map(),fromSMT(e, valueType))
          }
          // Need to recover value form function model
          val (cases, default) = extractCases(body)
          FiniteMap(cases.toSeq, default, keyType, valueType)
        } else {
          throw FatalError("Array on non-function or unknown symbol "+k)
        }

      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe @ SetType(base))) =>
        val fm @ FiniteMap(cases, dflt, _, _) = fromSMT(t, Some(MapType(base, BooleanType)))
        if (dflt != BooleanLiteral(false)) unsupported(fm, "Solver returned a co-finite set which is not supported")
        FiniteSet(cases.collect { case (k, BooleanLiteral(true)) => k }, base)

      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe @ BagType(base))) =>
        val fm @ FiniteMap(cases, dflt, _, _) = fromSMT(t, Some(MapType(base, IntegerType)))
        if (dflt != IntegerLiteral(0)) unsupported(fm, "Solver returned a co-finite bag which is not supported")
        FiniteBag(cases.filter(_._2 != IntegerLiteral(BigInt(0))), base)

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), Some(ArraysEx.ArraySort(k, v))),
        Seq(defV)
      ), Some(MapType(from, to))) =>
        FiniteMap(Seq(), fromSMT(defV, Some(to)), from, to)

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("store"), _), _),
        Seq(arr, key, elem)
      ), Some(mt @ MapType(from, to))) =>
        MapUpdated(fromSMT(arr, mt), fromSMT(key, from), fromSMT(elem, to))

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), Some(ArraysEx.ArraySort(k, v))),
        Seq(defV)
      ), Some(tpe @ SetType(base))) =>
        val dflt = fromSMT(defV, Some(BooleanType))
        if (dflt != BooleanLiteral(false)) unsupported(dflt, "Solver returned a co-finite set which is not supported")
        FiniteSet(Seq.empty, base)

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("store"), _), _),
        Seq(arr, key, elem)
      ), Some(st @ SetType(base))) =>
        val set = fromSMT(arr, st)
        IfExpr(fromSMT(elem, BooleanType), SetAdd(set, fromSMT(key, base)), set)

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), Some(ArraysEx.ArraySort(k, v))),
        Seq(defV)
      ), Some(tpe @ BagType(base))) =>
        val dflt = fromSMT(defV, Some(IntegerType))
        if (dflt != IntegerLiteral(BigInt(0))) unsupported(dflt, "Solver returned a co-finite bag which is not supported")
        FiniteBag(Seq.empty, base)

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("store"), _), _),
        Seq(arr, key, elem)
      ), Some(bt @ BagType(base))) =>
        BagUnion(fromSMT(arr, bt), FiniteBag(Seq(fromSMT(key, base) -> fromSMT(elem, IntegerType)), base))

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), Some(ArraysEx.ArraySort(k, v))),
        Seq(defV)
      ), None) =>
        val keyType = fromSMT(k)
        val valType = fromSMT(v)
        FiniteMap(Seq(), fromSMT(defV, valType), keyType, valType)

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("store"), _), _),
        Seq(arr, key, elem)
      ), None) =>
        MapUpdated(fromSMT(arr), fromSMT(key), fromSMT(elem))

      case _ =>
        super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {

    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems, base) =>
      declareSort(fs.getType)
      toSMT(FiniteMap(elems map ((_, BooleanLiteral(true))), BooleanLiteral(false), base, BooleanType))

    case SubsetOf(ss, s) =>
      // a isSubset b   ==>   (a zip b).map(implies) == (* => true)
      val allTrue = ArrayConst(declareSort(s.getType), True())
      SMTEquals(ArrayMap(SSymbol("implies"), toSMT(ss), toSMT(s)), allTrue)

    case SetAdd(s, e) =>
      ArraysEx.Store(toSMT(s), toSMT(e), True())

    case ElementOfSet(e, s) =>
      ArraysEx.Select(toSMT(s), toSMT(e))

    case SetDifference(a, b) =>
      // a -- b
      // becomes:
      // a && not(b)

      ArrayMap(SSymbol("and"), toSMT(a), ArrayMap(SSymbol("not"), toSMT(b)))

    case SetUnion(l, r) =>
      ArrayMap(SSymbol("or"), toSMT(l), toSMT(r))

    case SetIntersection(l, r) =>
      ArrayMap(SSymbol("and"), toSMT(l), toSMT(r))

    case fb @ FiniteBag(elems, base) =>
      val BagType(t) = fb.getType
      declareSort(BagType(t))
      toSMT(FiniteMap(elems, IntegerLiteral(0), t, IntegerType))

    case BagAdd(b, e) =>
      val bid = FreshIdentifier("b", true)
      val eid = FreshIdentifier("e", true)
      val (bSym, eSym) = (id2sym(bid), id2sym(eid))
      SMTLet(
        VarBinding(bSym, toSMT(b)), Seq(VarBinding(eSym, toSMT(e))),
        ArraysEx.Store(bSym, eSym, Ints.Add(ArraysEx.Select(bSym, eSym), Ints.NumeralLit(1)))
      )

    case MultiplicityInBag(e, b) =>
      ArraysEx.Select(toSMT(b), toSMT(e))

    case BagUnion(b1, b2) =>
      val plus = SortedSymbol("+", List(IntegerType, IntegerType).map(declareSort), declareSort(IntegerType))
      ArrayMap(plus, toSMT(b1), toSMT(b2))

    case BagIntersection(b1, b2) =>
      toSMT(BagDifference(b1, BagDifference(b1, b2)))

    case BagDifference(b1, b2) =>
      val abs   = SortedSymbol("abs", List(IntegerType).map(declareSort), declareSort(IntegerType))
      val plus  = SortedSymbol("+", List(IntegerType, IntegerType).map(declareSort), declareSort(IntegerType))
      val minus = SortedSymbol("-", List(IntegerType, IntegerType).map(declareSort), declareSort(IntegerType))
      val div   = SortedSymbol("/", List(IntegerType, IntegerType).map(declareSort), declareSort(IntegerType))

      val did = FreshIdentifier("d", true)
      val dSym = id2sym(did)

      val all2 = ArrayConst(declareSort(IntegerType), Ints.NumeralLit(2))

      SMTLet(
        VarBinding(dSym, ArrayMap(minus, toSMT(b1), toSMT(b2))), Seq(),
        ArrayMap(div, ArrayMap(plus, dSym, ArrayMap(abs, dSym)), all2)
      )

    case _ =>
      super.toSMT(e)
  }

  protected object SortedSymbol {
    def apply(op: String, from: List[Sort], to: Sort) = {
      def simpleSort(s: Sort): Boolean = s.subSorts.isEmpty && !s.id.isIndexed
      assert(from.forall(simpleSort) && simpleSort(to), "SortedSymbol is only defined for simple sorts")
      SList(SSymbol(op), SList(from.map(_.id.symbol): _*), to.id.symbol)
    }
  }

  protected object ArrayMap {
    def apply(op: SExpr, arrs: Term*) = {
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("map"), List(op)), None),
        arrs
      )
    }
  }

  protected object ArrayConst {
    def apply(sort: Sort, default: Term) = {
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const")), Some(sort)),
        List(default))
    }
  }
}
