/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Terms.{Identifier => SMTIdentifier, Let => SMTLet, _}
import _root_.smtlib.extensions.tip.Terms.{Lambda => SMTLambda, _}
import _root_.smtlib.trees.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.trees.CommandsResponses._
import _root_.smtlib.extensions.tip.Parser
import _root_.smtlib.extensions.tip.Lexer
import _root_.smtlib.lexer.Tokens
import _root_.smtlib.interpreters.Z3Interpreter
import _root_.smtlib.theories.Core.{Equals => SMTEquals, _}
import _root_.smtlib.theories.Operations._
import _root_.smtlib.theories._
import _root_.smtlib.theories.experimental._

import utils._

trait Z3Target extends SMTLIBTarget with SMTLIBDebugger {
  import context._
  import program._
  import program.trees._
  import program.symbols._

  def targetName = "z3"

  protected def interpreterOpts = Seq(
    "-in",
    "-smt2"
  )

  protected class Z3Parser(lexer: Lexer) extends Parser(lexer) {
    // Z3 uses a non-standard version of get-unsat-assumptions-response that
    // returns prop literals instead of symbols directly
    override def parseGetUnsatAssumptionsResponse: GetUnsatAssumptionsResponse = {
      nextToken match {
        case Tokens.SymbolLit("unsupported") => Unsupported
        case t => {
          check(t, Tokens.OParen)
          peekToken match {
            case Tokens.SymbolLit("error") =>
              eat(Tokens.SymbolLit("error"))
              val msg = parseString.value
              eat(Tokens.CParen)
              Error(msg)
            case t =>
              val props = parseUntil(Tokens.CParen)(parsePropLit _)
              GetUnsatAssumptionsResponseSuccess(props.map(_.symbol))
          }
        }
      }
    }
  }

  protected val interpreter = {
    val opts = interpreterOpts
    reporter.debug("Invoking solver "+targetName+" with "+opts.mkString(" "))
    new Z3Interpreter("z3", opts.toArray) {
      override lazy val parser: Z3Parser = new Z3Parser(new Lexer(out))
    }
  }

  // Z3 version 4.5.1 has disabled producing unsat assumptions by default,
  // so make sure it is enabled at this point.
  emit(SetOption(ProduceUnsatAssumptions(true)))

  protected class Version(val major: Int, val minor: Int, rest: String) extends Ordered[Version] {
    override def compare(that: Version): Int = {
      import scala.math.Ordering.Implicits._
      implicitly[Ordering[(Int, Int)]].compare((major, minor), (that.major, that.minor))
    }

    override def toString: String = s"$major.$minor.$rest"
  }

  protected object Version {
    def apply(major: Int, minor: Int): Version = new Version(major, minor, "")
  }

  protected lazy val version = emit(GetInfo(VersionInfoFlag())) match {
    case GetInfoResponseSuccess(VersionInfoResponse(version), _) =>
      val major +: minor +: rest = version.split("\\.").toSeq
      new Version(major.toInt, minor.toInt, rest.mkString("."))
    case r =>
      Version(0, 0) // We use 0.0 as an unknown default version
  }

  protected val extSym = SSymbol("_")

  protected lazy val setSort: SSymbol = {
    val s = SSymbol("InoxSet")
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
      declareSort(BooleanType())
      Sort(SMTIdentifier(setSort), Seq(declareSort(base)))
    case BagType(base) => declareSort(MapType(base, IntegerType()))
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

  protected def extractSet(e: Expr): Expr = e match {
    case FiniteMap(els, dflt, base, _) =>
      if (dflt != BooleanLiteral(false)) unsupported(dflt, "Solver returned a co-finite set which is not supported")
      if (els.forall(p => isValue(p._2))) FiniteSet(els.collect { case (e, BooleanLiteral(true)) => e }, base)
      else els.foldRight(FiniteSet(Seq.empty, base): Expr) { case ((k, v), s) => IfExpr(k, SetAdd(s, v), s) }
    case s: FiniteSet => s
    case _ => unsupported(e, "Expecting set expression in this position")
  }

  override protected def fromSMT(t: Term, otpe: Option[Type] = None)(implicit context: Context): Expr = {
    (t, otpe) match {
      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("is"), Seq(SSymbol(name))), None),
        Seq(e)
      ), _) if version >= Version(4, 6) && testers.containsB(SSymbol("is-" + name)) =>
        testers.toA(SSymbol("is-" + name)) match {
          case ac @ ADTCons(id, _) =>
            IsConstructor(fromSMT(e, ac.getType), id)
          case t =>
            unsupported(t, "woot? tester for non-adt type")
        }

      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe @ MapType(keyType, valueType))) =>
        val Some(Lambda(Seq(arg), body)) = context.getFunction(k, FunctionType(Seq(keyType), valueType))

        def extractCases(e: Expr): FiniteMap = e match {
          case Equals(argV, k) if valueType == BooleanType() && argV == arg.toVariable =>
            FiniteMap(Seq((k, BooleanLiteral(true))), BooleanLiteral(false), keyType, valueType)
          case IfExpr(Equals(argV, k), v, e) if argV == arg.toVariable =>
            val FiniteMap(elems, default, from, to) = extractCases(e)
            FiniteMap(elems :+ (k, v), default, from, to)
          case e => FiniteMap(Seq.empty, e, keyType, valueType)
        }
        extractCases(body)

      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe @ SetType(base))) =>
        val fm @ FiniteMap(cases, dflt, _, _) = fromSMT(t, Some(MapType(base, BooleanType())))
        if (dflt != BooleanLiteral(false)) unsupported(fm, "Solver returned a co-finite set which is not supported")
        FiniteSet(cases.collect { case (k, BooleanLiteral(true)) => k }, base)

      case (QualifiedIdentifier(ExtendedIdentifier(SSymbol("as-array"), k: SSymbol), _), Some(tpe @ BagType(base))) =>
        val fm @ FiniteMap(cases, dflt, _, _) = fromSMT(t, Some(MapType(base, IntegerType())))
        if (dflt != IntegerLiteral(0)) unsupported(fm, "Solver returned a co-finite bag which is not supported")
        FiniteBag(cases.filter(_._2 != IntegerLiteral(BigInt(0))), base)

      case (SMTLambda(Seq(SortedVar(s, sort)), term), Some(tpe @ MapType(keyType, valueType))) =>
        val arg = ValDef.fresh(s.name, fromSMT(sort))
        val body = fromSMT(term, Some(valueType))(context.withVariables(Seq(s -> arg.toVariable)))

        def extractCases(e: Expr): FiniteMap = e match {
          case Equals(argV, k) if valueType == BooleanType() && argV == arg.toVariable =>
            FiniteMap(Seq((k, BooleanLiteral(true))), BooleanLiteral(false), keyType, valueType)
          case IfExpr(Equals(argV, k), v, e) if argV == arg.toVariable =>
            val FiniteMap(elems, default, from, to) = extractCases(e)
            FiniteMap(elems :+ (k, v), default, from, to)
          case e => FiniteMap(Seq.empty, e, keyType, valueType)
        }
        extractCases(body)

      case (SMTLambda(Seq(arg), body), Some(tpe @ SetType(base))) =>
        val fm @ FiniteMap(cases, dflt, _, _) = fromSMT(t, Some(MapType(base, BooleanType())))
        if (dflt != BooleanLiteral(false)) unsupported(fm, "Solver returned a co-finite set which is not supported")
        FiniteSet(cases.collect { case (k, BooleanLiteral(true)) => k }, base)

      case (SMTLambda(Seq(arg), body), Some(tpe @ BagType(base))) =>
        val fm @ FiniteMap(cases, dflt, _, _) = fromSMT(t, Some(MapType(base, IntegerType())))
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
        val dflt = fromSMT(defV, Some(BooleanType()))
        if (dflt != BooleanLiteral(false)) unsupported(dflt, "Solver returned a co-finite set which is not supported")
        FiniteSet(Seq.empty, base)

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("store"), _), _),
        Seq(arr, key, elem)
      ), Some(st @ SetType(base))) =>
        val set = fromSMT(arr, st)
        IfExpr(fromSMT(elem, BooleanType()), SetAdd(set, fromSMT(key, base)), set)

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("map"),
          List(SList(List(SSymbol("or"), SList(List(SSymbol("Bool"), SSymbol("Bool"))), SSymbol("Bool"))))), None),
        Seq(s1, s2)
      ), _) =>
        fromSMTUnifyType(s1, s2, otpe)((e1, e2) => SetUnion(extractSet(e1), extractSet(e2)))

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("map"),
          List(SList(List(SSymbol("or"), SList(List(SSymbol("Bool"), SSymbol("Bool"))), SSymbol("Bool"))))), None),
        Seq(s1, s2)
      ), _) =>
        fromSMTUnifyType(s1, s2, otpe)((e1, e2) => SetIntersection(extractSet(e1), extractSet(e2)))

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("const"), _), Some(ArraysEx.ArraySort(k, v))),
        Seq(defV)
      ), Some(tpe @ BagType(base))) =>
        val dflt = fromSMT(defV, Some(IntegerType()))
        if (dflt != IntegerLiteral(BigInt(0))) unsupported(dflt, "Solver returned a co-finite bag which is not supported")
        FiniteBag(Seq.empty, base)

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("store"), _), _),
        Seq(arr, key, elem)
      ), Some(bt @ BagType(base))) =>
        BagUnion(fromSMT(arr, bt), FiniteBag(Seq(fromSMT(key, base) -> fromSMT(elem, IntegerType())), base))

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

      case (FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("map"),
          List(SList(List(SSymbol("ite"), SList(List(SSymbol("Bool"), maskT, map1T, map2T)), resT)))), None),
        Seq(mask, map1, map2)
      ), _) =>
        // TODO: unify the types maskT, map1T, map2T and resT, because they should all be equal
        MapMerge(fromSMT(mask, otpe), fromSMT(map1, otpe), fromSMT(map2, otpe))

      case _ =>
        super.fromSMT(t, otpe)
    }
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {

    case IsConstructor(e, id) if version >= Version(4, 6) =>
      val tpe @ ADTType(_, tps) = e.getType
      declareSort(tpe)
      val SSymbol(name) = testers.toB(ADTCons(id, tps))
      FunctionApplication(
        QualifiedIdentifier(SMTIdentifier(SSymbol("is"), Seq(SSymbol(name.drop(3)))), None),
        Seq(toSMT(e))
      )

    /**
     * ===== Set operations =====
     */
    case fs @ FiniteSet(elems, base) =>
      declareSort(fs.getType)
      toSMT(FiniteMap(elems map ((_, BooleanLiteral(true))), BooleanLiteral(false), base, BooleanType()))

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

    case MapMerge(mask, map1, map2) =>
      val s = declareSort(map1.getType.asInstanceOf[MapType].to)
      ArrayMap(SortedSymbol("ite", List(BoolSort(), s), s), toSMT(mask), toSMT(map1), toSMT(map2))

    case SetIntersection(l, r) =>
      ArrayMap(SSymbol("and"), toSMT(l), toSMT(r))

    case fb @ FiniteBag(elems, base) =>
      val BagType(t) = fb.getType
      declareSort(BagType(t))
      toSMT(FiniteMap(elems, IntegerLiteral(0), t, IntegerType()))

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
      val plus = SortedSymbol("+", List(IntegerType(), IntegerType()).map(declareSort), declareSort(IntegerType()))
      ArrayMap(plus, toSMT(b1), toSMT(b2))

    case BagIntersection(b1, b2) =>
      toSMT(BagDifference(b1, BagDifference(b1, b2)))

    case BagDifference(b1, b2) =>
      val abs   = SortedSymbol("abs", List(IntegerType()).map(declareSort), declareSort(IntegerType()))
      val plus  = SortedSymbol("+", List(IntegerType(), IntegerType()).map(declareSort), declareSort(IntegerType()))
      val minus = SortedSymbol("-", List(IntegerType(), IntegerType()).map(declareSort), declareSort(IntegerType()))
      val div   = SortedSymbol("div", List(IntegerType(), IntegerType()).map(declareSort), declareSort(IntegerType()))

      val did = FreshIdentifier("d", true)
      val dSym = id2sym(did)

      val all2 = ArrayConst(declareSort(b1.getType), Ints.NumeralLit(2))

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
