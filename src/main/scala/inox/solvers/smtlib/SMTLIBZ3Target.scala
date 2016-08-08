/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.common._
import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, Let => SMTLet, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.interpreters.Z3Interpreter
import _root_.smtlib.theories.Core.{Equals => SMTEquals, _}
import _root_.smtlib.theories._

trait SMTLIBZ3Target extends SMTLIBTarget {

  import program._
  import trees._
  import symbols._

  def targetName = "z3"

  def interpreterOps(ctx: InoxContext) = {
    Seq(
      "-in",
      "-smt2"
    )
  }

  def getNewInterpreter(ctx: InoxContext) = {
    val opts = interpreterOps(ctx)
    ctx.reporter.debug("Invoking solver "+targetName+" with "+opts.mkString(" "))

    new Z3Interpreter("z3", opts.toArray)
  }

  protected val extSym = SSymbol("_")

  protected var setSort: Option[SSymbol] = None

  override protected def declareSort(t: Type): Sort = {
    val tpe = normalizeType(t)
    sorts.cachedB(tpe) {
      tpe match {
        case SetType(base) =>
          super.declareSort(BooleanType)
          declareSetSort(base)
        case BagType(base) =>
          declareSort(MapType(base, IntegerType))
        case _ =>
          super.declareSort(t)
      }
    }
  }

  protected def declareSetSort(of: Type): Sort = {
    setSort match {
      case None =>
        val s = SSymbol("Set")
        val t = SSymbol("T")
        setSort = Some(s)

        val arraySort = Sort(SMTIdentifier(SSymbol("Array")),
                             Seq(Sort(SMTIdentifier(t)), BoolSort()))

        val cmd = DefineSort(s, Seq(t), arraySort)
        emit(cmd)

      case _ =>
    }

    Sort(SMTIdentifier(setSort.get), Seq(declareSort(of)))
  }

  override protected def fromSMT(t: Term, otpe: Option[Type] = None)
                                (implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {


    (t, otpe) match {
      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe)) =>
        if (letDefs contains k) {
          val MapType(keyType, valueType) = tpe
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
          FiniteMap(cases.toSeq, default, keyType)
        } else {
          throw FatalError("Array on non-function or unknown symbol "+k)
        }

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), Some(ArraysEx.ArraySort(k, v))),
        Seq(defV)
      ), Some(tpe)) =>
        val ktpe = sorts.fromB(k)
        val vtpe = sorts.fromB(v)
        FiniteMap(Seq(), fromSMT(defV), ktpe)

      case _ =>
        super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {

    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems, base) =>
      val st @ SetType(base) = fs.getType
      declareSort(st)
      toSMT(FiniteMap(elems map ((_, BooleanLiteral(true))), BooleanLiteral(false), BooleanType))

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
      toSMT(FiniteMap(elems, IntegerLiteral(0), t))

    case BagAdd(b, e) =>
      val bid = FreshIdentifier("b", true)
      val eid = FreshIdentifier("e", true)
      val (bSym, eSym) = (id2sym(bid), id2sym(eid))
      SMTLet(VarBinding(bSym, toSMT(b)), Seq(VarBinding(eSym, toSMT(e))), ArraysEx.Store(bSym, eSym,
        Ints.Add(ArraysEx.Select(bSym, eSym), Ints.NumeralLit(1))))

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

      SMTLet(VarBinding(dSym, ArrayMap(minus, toSMT(b1), toSMT(b2))), Seq(),
        ArrayMap(div, ArrayMap(plus, dSym, ArrayMap(abs, dSym)), all2))

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
