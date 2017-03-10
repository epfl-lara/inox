/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, Let => SMTLet, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.interpreters.Z3Interpreter
import _root_.smtlib.theories.Core.{Equals => SMTEquals, _}
import _root_.smtlib.theories.Operations._
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
    case StringType => Sort(SMTIdentifier(SSymbol("Seq")), Seq(declareSort(CharType)))
    case _ => super.computeSort(t)
  }

  override protected def id2sym(id: Identifier): SSymbol = {
    // @nv: Z3 uses identifiers of the shape 'k!\d+' to represent
    //      its array functions, so we have to make sure to avoid collisions!
    if (id.name == "k") {
      super.id2sym(FreshIdentifier("k0"))
    } else {
      super.id2sym(id)
    }
  }

  override protected def fromSMT(t: Term, otpe: Option[Type] = None)(implicit context: Context): Expr = {
    (t, otpe) match {
      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe @ MapType(keyType, valueType))) =>
        val Some(Lambda(Seq(arg), body)) = context.getFunction(k, FunctionType(Seq(keyType), valueType))

        def extractCases(e: Expr): FiniteMap = e match {
          case IfExpr(Equals(argV, k), v, e) if argV == arg.toVariable =>
            val FiniteMap(elems, default, from, to) = extractCases(e)
            FiniteMap(elems :+ (k, v), default, from, to)
          case e => FiniteMap(Seq.empty, e, keyType, valueType)
        }
        extractCases(body)

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

      case (StringLit(v), _) => StringLiteral(v)

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

    /** String operations */
    case StringLiteral(v) =>
      declareSort(StringType)
      StringLit(v)

    case StringLength(a) => SeqLength(toSMT(a))
    case StringConcat(a, b) => SeqConcat(toSMT(a), toSMT(b))
    case SubString(a, start, Plus(start2, length)) if start == start2 =>
      SeqExtract(toSMT(a), toSMT(start), toSMT(length))
    case SubString(a, start, end) =>
      SeqExtract(toSMT(a), toSMT(start), toSMT(Minus(end, start)))

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

  protected object StringLit {
    import FixedSizeBitVectors._

    def apply(str: String): Term = str.map(c => SeqUnit(toSMT(CharLiteral(c))(Map.empty))) match {
      case Seq() => QualifiedIdentifier(SMTIdentifier(SSymbol("seq.empty")), Some(declareSort(StringType)))
      case Seq(e) => e
      case h1 +: h2 +: rest => SeqConcat(h1, h2, rest : _*)
    }

    def unapply(term: Term): Option[String] = term match {
      case QualifiedIdentifier(SMTIdentifier(SSymbol("seq.empty"), _), Some(BitVectorSort(b))) if b == BigInt(16) => Some("")
      case QualifiedIdentifier(SMTIdentifier(SSymbol("seq.empty"), _), None) => Some("")
      case SeqUnit(BitVectorConstant(n, b)) if b == BigInt(16) => Some(n.toInt.toChar.toString)
      case SeqConcat(e1, e2, es @ _*) =>
        val optChars = (e1 +: e2 +: es).map {
          case BitVectorConstant(n, b) if b == BigInt(16) => Some(n.toInt.toChar.toString)
          case _ => None
        }
        if (optChars.forall(_.isDefined)) {
          Some(optChars.map(_.get).reduce(_ + _))
        } else {
          None
        }
      case _ => None
    }
  }

  protected object SeqUnit extends Operation1 { override val name = "seq.unit" }
  protected object SeqLength extends Operation1 { override val name = "seq.len" }
  protected object SeqConcat extends OperationN2 { override val name = "seq.++" }
  protected object SeqExtract extends Operation3 { override val name = "seq.extract" }
}
