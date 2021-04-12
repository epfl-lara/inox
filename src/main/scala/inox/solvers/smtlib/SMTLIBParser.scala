/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import utils._

import _root_.smtlib.lexer.{Tokens => LT, _}
import _root_.smtlib.trees.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.trees.Terms.{Let => SMTLet, Forall => SMTForall, Identifier => SMTIdentifier, _}
import _root_.smtlib.theories._
import _root_.smtlib.theories.experimental._
import _root_.smtlib.extensions.tip.Terms.{Lambda => SMTLambda, Application => SMTApplication, _}
import _root_.smtlib.extensions.tip.Commands._

import scala.collection.BitSet

class MissformedSMTException(term: _root_.smtlib.trees.Tree, reason: String)
  extends Exception("Missfomed SMT source in " + term + ":\n" + reason)

trait SMTLIBParser {
  val trees: ast.Trees
  val symbols: trees.Symbols
  import trees._
  import symbols._

  protected trait AbstractContext { self: Context =>
    val vars: Map[SSymbol, Expr]
    def withVariable(sym: SSymbol, expr: Expr): Context
    def withVariables(vars: Seq[(SSymbol, Expr)]): Context = vars.foldLeft(this)((ctx, p) => ctx withVariable (p._1, p._2))
  }

  protected type Context <: AbstractContext

  protected def fromSMT(sv: SortedVar)(implicit context: Context): ValDef = ValDef.fresh(sv.name.name, fromSMT(sv.sort))

  final protected def fromSMT(term: Term, tpe: Type)(implicit context: Context): Expr = fromSMT(term, Some(tpe))
  final protected def fromSMT(pair: (Term, Type))(implicit context: Context): Expr = fromSMT(pair._1, Some(pair._2))

  final protected def fromSMTUnifyType(t1: Term, t2: Term, otpe: Option[Type])
                                      (recons: (Expr, Expr) => Expr)
                                      (implicit context: Context): Expr = {
    val (e1, e2) = (fromSMT(t1, otpe), fromSMT(t2, otpe))
    if (otpe.isDefined || !(e1.isTyped ^ e2.isTyped)) {
      recons(e1, e2)
    } else {
      if (e1.isTyped) {
        recons(e1, fromSMT(t2, e1.getType))
      } else {
        recons(fromSMT(t1, e2.getType), e2)
      }
    }
  }

  protected def fromSMT(term: Term, otpe: Option[Type] = None)(implicit context: Context): Expr = term match {
    case QualifiedIdentifier(SimpleIdentifier(sym), None) if context.vars contains sym => context.vars(sym)

    case SMTLet(binding, bindings, term) =>
      val newContext = (binding +: bindings).foldLeft(context) {
        case (context, VarBinding(name, term)) => context.withVariable(name, fromSMT(term)(context))
      }
      fromSMT(term, otpe)(newContext)

    case SMTForall(sv, svs, term) =>
      val vds = (sv +: svs).map(fromSMT)
      val bindings = ((sv +: svs) zip vds).map(p => p._1.name -> p._2.toVariable)
      Forall(vds, fromSMT(term, BooleanType())(context.withVariables(bindings)))

    case Exists(sv, svs, term) =>
      val vds = (sv +: svs).map(fromSMT)
      val bindings = ((sv +: svs) zip vds).map(p => p._1.name -> p._2.toVariable)
      val body = fromSMT(term, BooleanType())(context.withVariables(bindings))
      Not(Forall(vds, Not(body).setPos(body)))

    case Core.ITE(cond, thenn, elze) =>
      IfExpr(fromSMT(cond, BooleanType()), fromSMT(thenn, otpe), fromSMT(elze, otpe))

    case SNumeral(n) => otpe match {
      case Some(RealType()) => FractionLiteral(n, 1)
      case _ => IntegerLiteral(n)
    }

    case FixedSizeBitVectors.BitVectorLit(bs) =>
      otpe match {
        case Some(BVType(signed, _)) =>
          BVLiteral(signed, BitSet.empty ++ bs.reverse.zipWithIndex.collect { case (true, i) => i + 1 }, bs.size)
        case Some(CharType()) =>
          val bv = BVLiteral(true, BitSet.empty ++ bs.reverse.zipWithIndex.collect { case (true, i) => i + 1 }, 16)
          CharLiteral(bv.toBigInt.toInt.toChar)
        case _ =>
          BVLiteral(true, BitSet.empty ++ bs.reverse.zipWithIndex.collect { case (true, i) => i + 1 }, bs.size)
      }

    case FixedSizeBitVectors.BitVectorConstant(n, size) => otpe match {
      case Some(BVType(signed, _)) => BVLiteral(signed, n, size.intValue)
      case Some(CharType()) => CharLiteral(n.toChar)
      case _ => BVLiteral(true, n, size.intValue)
    }

    case SDecimal(value) =>
      exprOps.normalizeFraction(FractionLiteral(
        value.bigDecimal.movePointRight(value.scale).toBigInteger,
        BigInt(10).pow(value.scale)))

    case SString(value) =>
      StringLiteral(utils.StringUtils.decode(value))

    case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("distinct")), None), args) =>
      val es = args.map(fromSMT(_))
      val tpEs = (if (es.exists(_.getType == Untyped) && es.exists(_.getType != Untyped)) {
        val tpe = leastUpperBound(es.map(_.getType).filter(_ != Untyped))
        if (tpe == Untyped) throw new MissformedSMTException(term, "Inconsistent types")
        args.map(fromSMT(_, tpe))
      } else {
        es
      }).toArray

      val indexPairs = args.indices.flatMap(i1 => args.indices.map(i2 => (i1, i2))).filter(p => p._1 != p._2)
      andJoin(indexPairs.map { p =>
        val (e1, e2) = (tpEs(p._1), tpEs(p._2))
        Not(Equals(e1, e2).setPos(e1)).setPos(e1)
      })

    case Core.Equals(e1, e2) => fromSMTUnifyType(e1, e2, None)(Equals)

    case Core.And(es @ _*) => And(es.map(fromSMT(_, BooleanType())))
    case Core.Or(es @ _*) => Or(es.map(fromSMT(_, BooleanType())))
    case Core.Implies(e1, e2) => Implies(fromSMT(e1, BooleanType()), fromSMT(e2, BooleanType()))
    case Core.Not(e) => Not(fromSMT(e, BooleanType()))

    case Core.True() => BooleanLiteral(true)
    case Core.False() => BooleanLiteral(false)

    /* Ints extractors cover the Reals operations as well */

    case Ints.Neg(e) => UMinus(fromSMT(e, otpe))
    case Ints.Add(e1, e2) => Plus(fromSMT(e1, otpe), fromSMT(e2, otpe))
    case Ints.Sub(e1, e2) => Minus(fromSMT(e1, otpe), fromSMT(e2, otpe))
    case Ints.Mul(e1, e2) => Times(fromSMT(e1, otpe), fromSMT(e2, otpe))

    case Ints.Div(e1, e2) => Division(fromSMT(e1, IntegerType()), fromSMT(e2, IntegerType()))
    case Ints.Mod(e1, e2) => Modulo(fromSMT(e1, IntegerType()), fromSMT(e2, IntegerType()))
    case Ints.Abs(e) =>
      val ie = fromSMT(e, IntegerType())
      IfExpr(
        LessThan(ie, IntegerLiteral(BigInt(0)).setPos(ie)).setPos(ie),
        UMinus(ie).setPos(ie),
        ie
      )

    case Ints.LessThan(e1, e2) => fromSMTUnifyType(e1, e2, None)(LessThan)
    case Ints.LessEquals(e1, e2) => fromSMTUnifyType(e1, e2, None)(LessEquals)
    case Ints.GreaterThan(e1, e2) => fromSMTUnifyType(e1, e2, None)(GreaterThan)
    case Ints.GreaterEquals(e1, e2) => fromSMTUnifyType(e1, e2, None)(GreaterEquals)

    case Reals.Div(SNumeral(n1), SNumeral(n2)) => FractionLiteral(n1, n2)
    case Reals.Div(e1, e2) => Division(fromSMT(e1, RealType()), fromSMT(e2, RealType()))

    case FixedSizeBitVectors.Not(e) => BVNot(fromSMT(e, otpe))
    case FixedSizeBitVectors.Neg(e) => UMinus(fromSMT(e, otpe))
    case FixedSizeBitVectors.And(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(BVAnd)
    case FixedSizeBitVectors.Or(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(BVOr)
    case FixedSizeBitVectors.XOr(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(BVXor)
    case FixedSizeBitVectors.Add(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(Plus)
    case FixedSizeBitVectors.Sub(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(Minus)
    case FixedSizeBitVectors.Mul(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(Times)
    case FixedSizeBitVectors.SDiv(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(Division)
    case FixedSizeBitVectors.UDiv(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(Division)
    case FixedSizeBitVectors.SRem(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(Remainder)
    case FixedSizeBitVectors.URem(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(Remainder)

    case FixedSizeBitVectors.SLessThan(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(LessThan)
    case FixedSizeBitVectors.SLessEquals(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(LessEquals)
    case FixedSizeBitVectors.SGreaterThan(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(GreaterThan)
    case FixedSizeBitVectors.SGreaterEquals(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(GreaterEquals)

    case FixedSizeBitVectors.ULessThan(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(LessThan)
    case FixedSizeBitVectors.ULessEquals(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(LessEquals)
    case FixedSizeBitVectors.UGreaterThan(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(GreaterThan)
    case FixedSizeBitVectors.UGreaterEquals(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(GreaterEquals)

    case FixedSizeBitVectors.ShiftLeft(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(BVShiftLeft)
    case FixedSizeBitVectors.AShiftRight(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(BVAShiftRight)
    case FixedSizeBitVectors.LShiftRight(e1, e2) => fromSMTUnifyType(e1, e2, otpe)(BVLShiftRight)

    case FixedSizeBitVectors.SignExtend(extend, e) =>
      val ast = fromSMT(e)
      val BVType(signed, current) = ast.getType
      val newSize = (current + extend).bigInteger.intValueExact
      BVWideningCast(ast, BVType(signed, newSize))

    case FixedSizeBitVectors.Extract(i, j, e) =>
      // Assume this is a Narrowing Cast, hence j must be 0
      if (j != 0) throw new MissformedSMTException(term, "Unexpected 'extract' which is not a narrowing cast")
      BVNarrowingCast(fromSMT(e), BVType(otpe match {
        case Some(BVType(signed, _)) => signed
        case _ => true
      }, (i + 1).bigInteger.intValueExact))

    case ArraysEx.Select(e1, e2) => otpe match {
      case Some(tpe) =>
        val ex2 = fromSMT(e2)
        MapApply(if (ex2.getType != Untyped) {
          fromSMT(e1, MapType(ex2.getType, tpe))
        } else {
          fromSMT(e1)
        }, ex2)
      case None =>
        MapApply(fromSMT(e1), fromSMT(e2))
    }

    case ArraysEx.Store(e1, e2, e3) => otpe match {
      case Some(MapType(from, to)) =>
        MapUpdated(fromSMT(e1, MapType(from, to)), fromSMT(e2, from), fromSMT(e2, to))
      case Some(_) =>
        throw new MissformedSMTException(term, "Unexpected non-map type for " + term)
      case None =>
        MapUpdated(fromSMT(e1), fromSMT(e2), fromSMT(e3))
    }

    case FunctionApplication(QualifiedIdentifier(SimpleIdentifier(SSymbol("const")), Some(sort)), Seq(dflt)) =>
      val d = fromSMT(dflt)
      val MapType(from, to) = fromSMT(sort)
      FiniteMap(Seq.empty, d, from, to)

    case _ => throw new MissformedSMTException(term, "Unknown SMT term")
  }

  protected def fromSMT(sort: Sort)(implicit context: Context): Type = sort match {
    case Sort(SMTIdentifier(SSymbol("bitvector" | "BitVec"), Seq(SNumeral(n))), Seq()) => BVType(true, n.toInt)
    case Sort(SimpleIdentifier(SSymbol("Bool")), Seq()) => BooleanType()
    case Sort(SimpleIdentifier(SSymbol("Int")), Seq()) => IntegerType()
    case Sort(SimpleIdentifier(SSymbol("Real")), Seq()) => RealType()
    case Sort(SimpleIdentifier(SSymbol("String")), Seq()) => StringType()
    case Sort(SimpleIdentifier(SSymbol("Array")), Seq(from, to)) => MapType(fromSMT(from), fromSMT(to))
    case _ => throw new MissformedSMTException(sort, "unexpected sort: " + sort)
  }
}
