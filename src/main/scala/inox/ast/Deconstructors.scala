/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import scala.collection.immutable.HashMap

/** Meat and bones of tree deconstruction/reconstruction.
  *
  * Implementations provide methods to extract all useful subtrees from
  * a given tree ([[Expressions.Expr]], [[Types.Type]], ...) as well as
  * a closure that can reconstruct the initial tree based on appropriate
  * arguments.
  *
  * Instances of [[Trees]] must provide a [[TreeDeconstructor]] as a
  * means of applying generic transformations to arbitrary extensions of
  * the [[Trees.Tree]] interface.
  *
  * @see [[Deconstructors]] for some interesting use cases
  */
trait TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  /** Rebuild a tree from the given set of identifiers, variables, subexpressions and types */
  protected type Builder[T <: t.Tree] = (Seq[Identifier], Seq[t.Variable], Seq[t.Expr], Seq[t.Type], Seq[t.Flag]) => T

  /** Extracted subtrees from a tree as well as a "builder" */
  protected type Deconstructed[T <: t.Tree] = (Seq[Identifier], Seq[s.Variable], Seq[s.Expr], Seq[s.Type], Seq[s.Flag], Builder[T])

  protected final val NoIdentifiers: Seq[Identifier] = Seq()
  protected final val NoVariables: Seq[s.Variable] = Seq()
  protected final val NoExpressions: Seq[s.Expr] = Seq()
  protected final val NoTypes: Seq[s.Type] = Seq()
  protected final val NoFlags: Seq[s.Flag] = Seq()

  /** Optimisation trick for large pattern matching sequence: jumps directly to the correct case based
    * on the type of the expression -- a kind of virtual table for pattern matching.
    *
    * NOTE using the following shorthand make things significantly slower,
    * even slower than ordering the regular pattern matching cases according
    * to their frequencies.
    *
    *     classOf[s.Not] -> { case s.Not(e) => ??? }
    *
    * NOTE this is only valid if each Expression class has no subtypes!
    * We keep expression types sealed to help ensure this issue doesn't ever appear.
    */
  private val exprTable: Map[Class[?], s.Expr => Deconstructed[t.Expr]] = HashMap(
    classOf[s.Assume] -> { expr =>
      val s.Assume(pred, body) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(pred, body), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Assume(es(0), es(1)))
    },
    classOf[s.Variable] -> { expr =>
      val v = expr.asInstanceOf[s.Variable]
      (NoIdentifiers, Seq(v), NoExpressions, NoTypes, NoFlags,
        (_,vs, _, _, _) => vs.head)
    },
    classOf[s.Let] -> { expr =>
      val s.Let(binder, e, body) = expr: @unchecked
      (NoIdentifiers, Seq(binder.toVariable), Seq(e, body), NoTypes, NoFlags,
        (_,vs, es, _, _) => t.Let(vs.head.toVal, es(0), es(1)))
    },
    classOf[s.Application] -> { expr =>
      val s.Application(caller, args) = expr: @unchecked
      (NoIdentifiers, NoVariables, caller +: args, NoTypes, NoFlags,
        (_, _, es, _, _) => t.Application(es.head, es.tail))
    },
    classOf[s.Lambda] -> { expr =>
      val s.Lambda(args, body) = expr: @unchecked
      (NoIdentifiers, args.map(_.toVariable), Seq(body), NoTypes, NoFlags,
        (_, vs, es, _, _) => t.Lambda(vs.map(_.toVal), es.head))
    },
    classOf[s.Forall] -> { expr =>
      val s.Forall(args, body) = expr: @unchecked
      (NoIdentifiers, args.map(_.toVariable), Seq(body), NoTypes, NoFlags,
        (_, vs, es, _, _) => t.Forall(vs.map(_.toVal), es.head))
    },
    classOf[s.Choose] -> { expr =>
      val s.Choose(res, pred) = expr: @unchecked
      (NoIdentifiers, Seq(res.toVariable), Seq(pred), NoTypes, NoFlags,
        (_, vs, es, _, _) => t.Choose(vs.head.toVal, es.head))
    },
    classOf[s.FunctionInvocation] -> { expr =>
      val s.FunctionInvocation(id, tps, args) = expr: @unchecked
      (Seq(id), NoVariables, args, tps, NoFlags,
        (ids, _, es, tps, _) => t.FunctionInvocation(ids.head, tps, es))
    },
    classOf[s.IfExpr] -> { expr =>
      val s.IfExpr(cond, thenn, elze) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(cond, thenn, elze), NoTypes, NoFlags,
        (_, _, es, _, _) => t.IfExpr(es(0), es(1), es(2)))
    },
    classOf[s.CharLiteral] -> { expr =>
      val s.CharLiteral(ch) = expr: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.CharLiteral(ch))
    },
    classOf[s.BVLiteral] -> { expr =>
      val s.BVLiteral(signed, bits, size) = expr: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.BVLiteral(signed, bits, size))
    },
    classOf[s.FPLiteral] -> { expr =>
      val s.FPLiteral(exponent, significand, bits) = expr: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.FPLiteral(exponent, significand, bits))
    },
    classOf[s.IntegerLiteral] -> { expr =>
      val s.IntegerLiteral(i) = expr: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.IntegerLiteral(i))
    },
    classOf[s.FractionLiteral] -> { expr =>
      val s.FractionLiteral(n, d) = expr: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.FractionLiteral(n, d))
    },
    classOf[s.BooleanLiteral] -> { expr =>
      val s.BooleanLiteral(b) = expr: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.BooleanLiteral(b))
    },
    classOf[s.StringLiteral] -> { expr =>
      val s.StringLiteral(st) = expr: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.StringLiteral(st))
    },
    classOf[s.UnitLiteral] -> { expr =>
      val s.UnitLiteral() = expr: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.UnitLiteral())
    },
    classOf[s.GenericValue] -> { expr =>
      val s.GenericValue(tp, id) = expr: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, Seq(tp), NoFlags,
        (_, _, _, tps, _) => t.GenericValue(tps.head.asInstanceOf[t.TypeParameter], id))
    },
    classOf[s.ADT] -> { expr =>
      val s.ADT(id, tps, args) = expr: @unchecked
      (Seq(id), NoVariables, args, tps, NoFlags,
        (ids, _, es, tps, _) => t.ADT(ids.head, tps, es))
    },
    classOf[s.IsConstructor] -> { expr =>
      val s.IsConstructor(e, id) = expr: @unchecked
      (Seq(id), NoVariables, Seq(e), NoTypes, NoFlags,
        (ids, _, es, _, _) => t.IsConstructor(es.head, ids.head))
    },
    classOf[s.ADTSelector] -> { expr =>
      val s.ADTSelector(e, sel) = expr: @unchecked
      (Seq(sel), NoVariables, Seq(e), NoTypes, NoFlags,
        (ids, _, es, _, _) => t.ADTSelector(es.head, ids.head))
    },
    classOf[s.Equals] -> { expr =>
      val s.Equals(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Equals(es(0), es(1)))
    },
    classOf[s.And] -> { expr =>
      val s.And(args) = expr: @unchecked
      (NoIdentifiers, NoVariables, args, NoTypes, NoFlags,
        (_, _, es, _, _) => t.And(es))
    },
    classOf[s.Or] -> { expr =>
      val s.Or(args) = expr: @unchecked
      (NoIdentifiers, NoVariables, args, NoTypes, NoFlags,
        (_, _, es, _, _) => t.Or(es))
    },
    classOf[s.Implies] -> { expr =>
      val s.Implies(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Implies(es(0), es(1)))
    },
    classOf[s.Not] -> { expr =>
      val s.Not(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Not(es.head))
    },
    classOf[s.StringConcat] -> { expr =>
      val s.StringConcat(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.StringConcat(es(0), es(1)))
    },
    classOf[s.SubString] -> { expr =>
      val s.SubString(t1, a, b) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, a, b), NoTypes, NoFlags,
        (_, _, es, _, _) => t.SubString(es(0), es(1), es(2)))
    },
    classOf[s.StringLength] -> { expr =>
      val s.StringLength(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.StringLength(es.head))
    },
    classOf[s.Plus] -> { expr =>
      val s.Plus(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Plus(es(0), es(1)))
    },
    classOf[s.Minus] -> { expr =>
      val s.Minus(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Minus(es(0), es(1)))
    },
    classOf[s.UMinus] -> { expr =>
      val s.UMinus(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.UMinus(es.head))
    },
    classOf[s.Times] -> { expr =>
      val s.Times(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Times(es(0), es(1)))
    },
    classOf[s.Division] -> { expr =>
      val s.Division(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Division(es(0), es(1)))
    },
    classOf[s.Remainder] -> { expr =>
      val s.Remainder(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Remainder(es(0), es(1)))
    },
    classOf[s.Modulo] -> { expr =>
      val s.Modulo(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Modulo(es(0), es(1)))
    },
    classOf[s.LessThan] -> { expr =>
      val s.LessThan(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.LessThan(es(0), es(1)))
    },
    classOf[s.GreaterThan] -> { expr =>
      val s.GreaterThan(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.GreaterThan(es(0), es(1)))
    },
    classOf[s.LessEquals] -> { expr =>
      val s.LessEquals(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.LessEquals(es(0), es(1)))
    },
    classOf[s.GreaterEquals] -> { expr =>
      val s.GreaterEquals(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.GreaterEquals(es(0), es(1)))
    },
    classOf[s.BVNot] -> { expr =>
      val s.BVNot(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BVNot(es.head))
    },
    classOf[s.BVAnd] -> { expr =>
      val s.BVAnd(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BVAnd(es(0), es(1)))
    },
    classOf[s.BVOr] -> { expr =>
      val s.BVOr(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BVOr(es(0), es(1)))
    },
    classOf[s.BVXor] -> { expr =>
      val s.BVXor(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BVXor(es(0), es(1)))
    },
    classOf[s.BVShiftLeft] -> { expr =>
      val s.BVShiftLeft(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BVShiftLeft(es(0), es(1)))
    },
    classOf[s.BVAShiftRight] -> { expr =>
      val s.BVAShiftRight(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BVAShiftRight(es(0), es(1)))
    },
    classOf[s.BVLShiftRight] -> { expr =>
      val s.BVLShiftRight(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BVLShiftRight(es(0), es(1)))
    },
    classOf[s.BVNarrowingCast] -> { expr =>
      val s.BVNarrowingCast(e, bvt) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), Seq(bvt), NoFlags,
        (_, _, es, tps, _) => t.BVNarrowingCast(es(0), tps(0).asInstanceOf[t.BVType]))
    },
    classOf[s.BVWideningCast] -> { expr =>
      val s.BVWideningCast(e, bvt) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), Seq(bvt), NoFlags,
        (_, _, es, tps, _) => t.BVWideningCast(es(0), tps(0).asInstanceOf[t.BVType]))
    },
    classOf[s.BVUnsignedToSigned] -> { expr =>
      val s.BVUnsignedToSigned(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BVUnsignedToSigned(es(0)))
    },
    classOf[s.BVSignedToUnsigned] -> { expr =>
      val s.BVSignedToUnsigned(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BVSignedToUnsigned(es(0)))
    },
    classOf[s.FPEquals] -> { expr =>
      val s.FPEquals(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPEquals(es(0), es(1)))
    },
    classOf[s.FPAdd] -> { expr =>
      val s.FPAdd(rm, t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(rm, t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPAdd(es(0), es(1), es(2)))
    },
    classOf[s.FPUMinus] -> { expr =>
      val s.FPUMinus(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPUMinus(es.head))
    },
    classOf[s.FPSub] -> { expr =>
      val s.FPSub(rm, t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(rm, t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPSub(es(0), es(1), es(2)))
    },
    classOf[s.FPMul] -> { expr =>
      val s.FPMul(rm, t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(rm, t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPMul(es(0), es(1), es(2)))
    },
    classOf[s.FPDiv] -> { expr =>
      val s.FPDiv(rm, t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(rm, t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPDiv(es(0), es(1), es(2)))
    },
    classOf[s.FPAbs] -> { expr =>
      val s.FPAbs(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPAbs(es(0)))
    },
    classOf[s.Sqrt] -> { expr =>
      val s.Sqrt(rm, e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(rm, e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.Sqrt(es(0), es(1)))
    },
    classOf[s.FPCast] -> { expr =>
      val s.FPCast(eb, sb, rm, e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(rm, e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPCast(eb, sb, es(0), es(1)))
    },
    classOf[s.FPLessThan] -> { expr =>
      val s.FPLessThan(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPLessThan(es(0), es(1)))
    },
    classOf[s.FPGreaterThan] -> { expr =>
      val s.FPGreaterThan(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPGreaterThan(es(0), es(1)))
    },
    classOf[s.FPLessEquals] -> { expr =>
      val s.FPLessEquals(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPLessEquals(es(0), es(1)))
    },
    classOf[s.FPGreaterEquals] -> { expr =>
      val s.FPGreaterEquals(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPGreaterEquals(es(0), es(1)))
    },
    classOf[s.FPIsZero] -> { expr =>
      val s.FPIsZero(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPIsZero(es(0)))
    },
    classOf[s.FPIsNaN] -> { expr =>
      val s.FPIsNaN(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPIsNaN(es(0)))
    },
    classOf[s.FPIsPositive] -> { expr =>
      val s.FPIsPositive(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPIsPositive(es(0)))
    },
    classOf[s.FPIsNegative] -> { expr =>
      val s.FPIsNegative(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPIsNegative(es(0)))
    },
    classOf[s.FPIsInfinite] -> { expr =>
      val s.FPIsInfinite(e) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.FPIsInfinite(es(0)))
    },
    classOf[s.RoundTowardZero.type] -> { expr =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.RoundTowardZero)
    },
    classOf[s.RoundTowardNegative.type] -> { expr =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.RoundTowardNegative)
    },
    classOf[s.RoundTowardPositive.type] -> { expr =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.RoundTowardPositive)
    },
    classOf[s.RoundNearestTiesToAway.type] -> { expr =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.RoundNearestTiesToAway)
    },
    classOf[s.RoundNearestTiesToEven.type] -> { expr =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.RoundNearestTiesToEven)
    },
    classOf[s.Tuple] -> { expr =>
      val s.Tuple(args) = expr: @unchecked
      (NoIdentifiers, NoVariables, args, NoTypes, NoFlags,
        (_, _, es, _, _) => t.Tuple(es))
    },
    classOf[s.TupleSelect] -> { expr =>
      val s.TupleSelect(e, i) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
        (_, _, es, _, _) => t.TupleSelect(es.head, i))
    },
    classOf[s.FiniteSet] -> { expr =>
      val s.FiniteSet(els, base) = expr: @unchecked
      (NoIdentifiers, NoVariables, els, Seq(base), NoFlags,
        (_, _, els, tps, _) => t.FiniteSet(els, tps.head))
    },
    classOf[s.SetAdd] -> { expr =>
      val s.SetAdd(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.SetAdd(es(0), es(1)))
    },
    classOf[s.ElementOfSet] -> { expr =>
      val s.ElementOfSet(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.ElementOfSet(es(0), es(1)))
    },
    classOf[s.SubsetOf] -> { expr =>
      val s.SubsetOf(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.SubsetOf(es(0), es(1)))
    },
    classOf[s.SetIntersection] -> { expr =>
      val s.SetIntersection(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.SetIntersection(es(0), es(1)))
    },
    classOf[s.SetUnion] -> { expr =>
      val s.SetUnion(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.SetUnion(es(0), es(1)))
    },
    classOf[s.SetDifference] -> { expr =>
      val s.SetDifference(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.SetDifference(es(0), es(1)))
    },
    classOf[s.FiniteBag] -> { expr =>
      val s.FiniteBag(els, base) = expr: @unchecked
      val subArgs = els.flatMap { case (k, v) => Seq(k, v) }
      (NoIdentifiers, NoVariables, subArgs, Seq(base), NoFlags,
        (_, _, as: Seq[t.Expr], tps: Seq[t.Type], _) => {
          def rec(kvs: Seq[t.Expr]): Seq[(t.Expr, t.Expr)] = kvs match {
            case Seq(k, v, t @ _*) =>
              Seq(k -> v) ++ rec(t)
            case Seq() => Seq()
            case _ => sys.error("odd number of key/value expressions")
          }
          t.FiniteBag(rec(as), tps.head)
        })
    },
    classOf[s.BagAdd] -> { expr =>
      val s.BagAdd(e1, e2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e1, e2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BagAdd(es(0), es(1)))
    },
    classOf[s.MultiplicityInBag] -> { expr =>
      val s.MultiplicityInBag(e1, e2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e1, e2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.MultiplicityInBag(es(0), es(1)))
    },
    classOf[s.BagIntersection] -> { expr =>
      val s.BagIntersection(e1, e2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e1, e2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BagIntersection(es(0), es(1)))
    },
    classOf[s.BagUnion] -> { expr =>
      val s.BagUnion(e1, e2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e1, e2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BagUnion(es(0), es(1)))
    },
    classOf[s.BagDifference] -> { expr =>
      val s.BagDifference(e1, e2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(e1, e2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.BagDifference(es(0), es(1)))
    },
    classOf[s.FiniteMap] -> { expr =>
      val s.FiniteMap(elems, default, kT, vT) = expr: @unchecked
      val subArgs = elems.flatMap { case (k, v) => Seq(k, v) } :+ default
      (NoIdentifiers, NoVariables, subArgs, Seq(kT, vT), NoFlags,
        (_, _, as: Seq[t.Expr], tps: Seq[t.Type], _) => {
          def rec(kvs: Seq[t.Expr]): (Seq[(t.Expr, t.Expr)], t.Expr) = kvs match {
            case Seq(k, v, t @ _*) =>
              val (kvs, default) = rec(t)
              (Seq(k -> v) ++ kvs, default)
            case Seq(default) => (Seq(), default)
          }
          val (pairs, default) = rec(as)
          t.FiniteMap(pairs, default, tps(0), tps(1))
        })
    },
    classOf[s.MapApply] -> { expr =>
      val s.MapApply(t1, t2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(t1, t2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.MapApply(es(0), es(1)))
    },
    classOf[s.MapUpdated] -> { expr =>
      val s.MapUpdated(map, k, v) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(map, k, v), NoTypes, NoFlags,
        (_, _, es, _, _) => t.MapUpdated(es(0), es(1), es(2)))
    },
    classOf[s.MapMerge] -> { expr =>
      val s.MapMerge(mask, map1, map2) = expr: @unchecked
      (NoIdentifiers, NoVariables, Seq(mask, map1, map2), NoTypes, NoFlags,
        (_, _, es, _, _) => t.MapMerge(es(0), es(1), es(2)))
    }
  )

  def deconstruct(expr: s.Expr): Deconstructed[t.Expr] = exprTable(expr.getClass)(expr)


  /** Same optimisation as for `deconstruct(expr: s.Expr)`. */
  private val typeTable: Map[Class[?], s.Type => Deconstructed[t.Type]] = HashMap(
    classOf[s.ADTType] -> { tpe =>
      val s.ADTType(id, ts) = tpe: @unchecked
      (Seq(id), NoVariables, NoExpressions, ts, NoFlags,
        (ids, _, _, ts, _) => t.ADTType(ids.head, ts))
    },
    classOf[s.TupleType] -> { tpe =>
      val s.TupleType(ts) = tpe: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, ts, NoFlags,
        (_, _, _, ts, _) => t.TupleType(ts))
    },
    classOf[s.SetType] -> { tpe =>
      val s.SetType(tp) = tpe: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, Seq(tp), NoFlags,
        (_, _, _, ts, _) => t.SetType(ts.head))
    },
    classOf[s.BagType] -> { tpe =>
      val s.BagType(tp) = tpe: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, Seq(tp), NoFlags,
        (_, _, _, ts, _) => t.BagType(ts.head))
    },
    classOf[s.MapType] -> { tpe =>
      val s.MapType(from,to) = tpe: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, Seq(from, to), NoFlags,
        (_, _, _, ts, _) => t.MapType(ts(0), ts(1)))
    },
    classOf[s.FunctionType] -> { tpe =>
      val s.FunctionType(fts, tt) = tpe: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, tt +: fts, NoFlags,
        (_, _, _, ts, _) => t.FunctionType(ts.tail.toList, ts.head))
    },
    classOf[s.TypeParameter] -> { tpe =>
      val s.TypeParameter(id, flags) = tpe: @unchecked
      (Seq(id), NoVariables, NoExpressions, NoTypes, flags,
        (ids, _, _, _, flags) => t.TypeParameter(ids.head, flags))
    },
    classOf[s.BVType] -> { tpe =>
      val s.BVType(signed, size) = tpe: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.BVType(signed, size))
    },
    classOf[s.FPType] -> { tpe =>
      val s.FPType(exponent, significand) = tpe: @unchecked
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.FPType(exponent, significand))
    },
    classOf[s.RoundingMode.type] -> { tpe =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags,
        (_, _, _, _, _) => t.RoundingMode)
    },
    // @nv: can't use `s.Untyped.getClass` as it is not yet created at this point
    scala.reflect.classTag[s.Untyped.type].runtimeClass -> { _ =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags, (_, _, _, _, _) => t.Untyped)
    },

    classOf[s.BooleanType] -> { _ =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags, (_, _, _, _, _) => t.BooleanType())
    },
    classOf[s.UnitType] -> { _ =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags, (_, _, _, _, _) => t.UnitType())
    },
    classOf[s.CharType] -> { _ =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags, (_, _, _, _, _) => t.CharType())
    },
    classOf[s.IntegerType] -> { _ =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags, (_, _, _, _, _) => t.IntegerType())
    },
    classOf[s.RealType] -> { _ =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags, (_, _, _, _, _) => t.RealType())
    },
    classOf[s.StringType] -> { _ =>
      (NoIdentifiers, NoVariables, NoExpressions, NoTypes, NoFlags, (_, _, _, _, _) => t.StringType())
    },

    classOf[s.PiType] -> { tpe =>
      val s.PiType(params, to) = tpe: @unchecked
      (NoIdentifiers, params.map(_.toVariable), NoExpressions, Seq(to), NoFlags,
        (_, vs, _, tps, _) => t.PiType(vs.map(_.toVal), tps.head))
    },
    classOf[s.SigmaType] -> { tpe =>
      val s.SigmaType(params, to) = tpe: @unchecked
      (NoIdentifiers, params.map(_.toVariable), NoExpressions, Seq(to), NoFlags,
        (_, vs, _, tps, _) => t.SigmaType(vs.map(_.toVal), tps.head))
    },
    classOf[s.RefinementType] -> { tpe =>
      val s.RefinementType(vd, pred) = tpe: @unchecked
      (NoIdentifiers, Seq(vd.toVariable), Seq(pred), NoTypes, NoFlags,
        (_, vs, es, _, _) => t.RefinementType(vs.head.toVal, es.head))
    }
  )

  def deconstruct(tpe: s.Type): Deconstructed[t.Type] = typeTable(tpe.getClass)(tpe)

  /** Rebuild a flag from the given set of identifiers, expressions and types */
  protected type FlagBuilder = (Seq[Identifier], Seq[t.Expr], Seq[t.Type]) => t.Flag

  /** Extracted subtrees from a flag as well as a "builder" */
  protected type DeconstructedFlag = (Seq[Identifier], Seq[s.Expr], Seq[s.Type], FlagBuilder)

  def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.HasADTInvariant(id) =>
      (Seq(id), Seq(), Seq(), (ids, _, _) => t.HasADTInvariant(ids.head))
    case s.HasADTEquality(id) =>
      (Seq(id), Seq(), Seq(), (ids, _, _) => t.HasADTEquality(ids.head))
    case s.Annotation(name, args) =>
      val withIndex = args.zipWithIndex
      val (exprs, exprIndexes) = withIndex.collect { case (e: s.Expr, i) => e -> i }.unzip
      val (types, typeIndexes) = withIndex.collect { case (tp: s.Type, i) => tp -> i }.unzip

      // we use the implicit contract on Flags here that states that a flag is either
      // an instance of Expr | Type, or it has nothing to do with a tree
      val rest = withIndex.filterNot(_._1.isInstanceOf[s.Tree])
      (Seq(), exprs, types, (_, es, tps) => t.Annotation(name,
        ((es zip exprIndexes) ++ (tps zip typeIndexes) ++ rest).sortBy(_._2).map(_._1)
      ))
  }
}

/** Provides extraction capabilities to [[Trees]] based on a
  * [[TreeDeconstructor]] instance. */
trait Deconstructors { self: Trees =>

  def getDeconstructor(that: Trees): TreeDeconstructor {
    val s: self.type
    val t: that.type
  } = {
    class TreeDeconstructorImpl(override val s: self.type, override val t: that.type) extends TreeDeconstructor
    new TreeDeconstructorImpl(self, that)
  }

  val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  } = getDeconstructor(self)

  /** Operator Extractor to extract any Expression in a consistent way.
    *
    * You can match on any Inox Expr, and then get both a Seq[Expr] of
    * subterms and a builder function that takes a Seq of subterms (of same
    * length) and rebuild the original node.
    *
    * Those extractors do not perform any syntactic simplifications. They
    * rebuild the node using the case class (not the constructor, that performs
    * simplifications). The rational behind this decision is to have core
    * tools for performing tree transformations that are very predictable, if
    * one need to simplify the tree, it is easy to write/call a simplification
    * function that would simply apply the corresponding constructor for each node.
    */
  val Operator: TreeExtractor { val s: self.type; val t: self.type; type Source = Expr; type Target = Expr } = {
    class OperatorImpl(override protected val s: self.type,
                       override protected val t: self.type) extends TreeExtractor {
      type Source = Expr
      type Target = Expr

      def unapply(e: Expr): Option[(Seq[Expr], Seq[Expr] => Expr)] = {
        val (ids, vs, es, tps, flags, builder) = deconstructor.deconstruct(e)
        Some(es, ess => builder(ids, vs, ess, tps, flags))
      }
    }
    new OperatorImpl(self, self)
  }

  object TopLevelOrs { // expr1 OR (expr2 OR (expr3 OR ..)) => List(expr1, expr2, expr3)
    def unapply(e: Expr): Option[Seq[Expr]] = e match {
      case Let(i, e, TopLevelOrs(bs)) => Some(bs map (Let(i,e,_)))
      case Or(exprs) =>
        Some(exprs.flatMap(unapply).flatten)
      case e =>
        Some(Seq(e))
    }
  }

  object TopLevelAnds { // expr1 AND (expr2 AND (expr3 AND ..)) => List(expr1, expr2, expr3)
    def unapply(e: Expr): Option[Seq[Expr]] = e match {
      case Let(i, e, TopLevelAnds(bs)) => Some(bs map (Let(i,e,_)))
      case And(exprs) =>
        Some(exprs.flatMap(unapply).flatten)
      case e =>
        Some(Seq(e))
    }
  }

  object CNF {
    def unapply(e: Expr): Option[Seq[Expr]] = Some(exprOps.toCNF(e))
  }

  object IsTyped {
    def unapply[T <: Typed](e: T)(using Symbols): Option[(T, Type)] = Some((e, e.getType))
  }

  def unwrapTuple(e: Expr, isTuple: Boolean)(using s: Symbols): Seq[Expr] = e.getType match {
    case TupleType(subs) if isTuple =>
      for (ind <- 1 to subs.size) yield { s.tupleSelect(e, ind, isTuple) }
    case _ if !isTuple => Seq(e)
    case tp => sys.error(s"Calling unwrapTuple on non-tuple $e of type $tp")
  }

  def unwrapTuple(e: Expr, expectedSize: Int)(using Symbols): Seq[Expr] = unwrapTuple(e, expectedSize > 1)

  def unwrapTupleType(tp: Type, isTuple: Boolean): Seq[Type] = tp match {
    case TupleType(subs) if isTuple => subs
    case tp if !isTuple => Seq(tp)
    case tp => sys.error(s"Calling unwrapTupleType on $tp")
  }

  def unwrapTupleType(tp: Type, expectedSize: Int): Seq[Type] =
    unwrapTupleType(tp, expectedSize > 1)
}
