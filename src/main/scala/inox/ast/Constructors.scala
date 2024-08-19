/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import inox.utils.{Position, NoPosition}

/** Provides constructors for [[Expressions]].
  *
  * The constructors implement some logic to simplify the tree and
  * potentially use a different expression node if one is more suited.
  * @define encodingof Encoding of
  */
trait Constructors { self: Trees =>

  /** Wraps the sequence of expressions as a tuple. If the sequence contains a single expression,
    * it is returned instead.
    * @see [[Expressions.Tuple Tuple]]
    */
  def tupleWrap(es: Seq[Expr]): Expr = es match {
    case Seq() => UnitLiteral()
    case Seq(elem) => elem
    case more => Tuple(more)
  }

  /** Wraps the sequence of types as a tuple. If the sequence contains a single type, it is returned instead.
    * If the sequence is empty, the [[Types.UnitType UnitType]] is returned.
    * @see [[Types.TupleType]]
    */
  def tupleTypeWrap(tps: Seq[Type]): Type = tps match {
    case Seq() => UnitType()
    case Seq(elem) => elem
    case more => TupleType(more)
  }

  /** $encodingof `&&`-expressions with arbitrary number of operands, and simplified.
    * @see [[Expressions.And And]]
    */
  def and(exprs: Expr*): Expr = {
    val flat = exprs.flatMap {
      case And(es) => es
      case o => Seq(o)
    }

    var stop = false
    val simpler = (for (e <- flat if !stop && e != BooleanLiteral(true)) yield {
      if (e == BooleanLiteral(false)) stop = true
      e
    }).distinct

    val defaultPos = exprs match {
      case Seq() => NoPosition
      case es => Position.between(es.head.getPos, es.last.getPos)
    }

    simpler match {
      case Seq()  => BooleanLiteral(true).setPos(defaultPos)
      case Seq(x) => x
      case _      => And(simpler).setPos(defaultPos)
    }
  }

  /** $encodingof `&&`-expressions with arbitrary number of operands as a sequence, and simplified.
    * @see [[Expressions.And And]]
    */
  def andJoin(es: Seq[Expr]): Expr = and(es*)

  /** $encodingof `||`-expressions with arbitrary number of operands, and simplified.
    * @see [[Expressions.Or Or]]
    */
  def or(exprs: Expr*): Expr = {
    val flat = exprs.flatMap {
      case Or(es) => es
      case o => Seq(o)
    }

    var stop = false
    val simpler = (for(e <- flat if !stop && e != BooleanLiteral(false)) yield {
      if(e == BooleanLiteral(true)) stop = true
      e
    }).distinct

    val defaultPos = exprs match {
      case Seq() => NoPosition
      case es => Position.between(es.head.getPos, es.last.getPos)
    }

    simpler match {
      case Seq()  => BooleanLiteral(false).setPos(defaultPos)
      case Seq(x) => x
      case _      => Or(simpler).setPos(defaultPos)
    }
  }

  /** $encodingof `||`-expressions with arbitrary number of operands as a sequence, and simplified.
    * @see [[Expressions.Or Or]]
    */
  def orJoin(es: Seq[Expr]): Expr = or(es*)

  /** $encodingof simplified `!`-expressions .
    * @see [[Expressions.Not Not]]
    */
  def not(e: Expr): Expr = exprOps.negate(e)

  /** $encodingof simplified `... ==> ...` (implication)
    * @see [[Expressions.Implies Implies]]
    */
  def implies(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (BooleanLiteral(false), _) => BooleanLiteral(true)
    case (_, BooleanLiteral(true))  => BooleanLiteral(true)
    case (BooleanLiteral(true), r)  => r
    case (l, BooleanLiteral(false)) => Not(l)
    case (l1, Implies(l2, r2))      => implies(and(l1, l2), r2)
    case _                          => Implies(lhs, rhs)
  }

  /** $encodingof simplified `... == ...` (equality).
    * @see [[Expressions.Equals Equals]]
    */
  // @mk I simplified that because it seemed dangerous and unnessecary
  def equality(a: Expr, b: Expr): Expr = {
    if (a.isInstanceOf[Terminal] && a == b ) {
      BooleanLiteral(true)
    } else if (a.isInstanceOf[Literal[?]] && b.isInstanceOf[Literal[?]]) {
      BooleanLiteral(a == b)
    } else {
      Equals(a, b)
    }
  }

  /** $encodingof simplified `assume(pred, body)` (assumption).
    * Transforms
    * {{{ assume(assume(pred1, pred2), body) }}}
    * and
    * {{{ assume(pred1, assume(pred2, body)) }}}
    * into
    * {{{ assume(pred1 && pred2, body) }}}
    * @see [[Expressions.Assume Assume]]
    */
  def assume(pred: Expr, body: Expr): Expr = (pred, body) match {
    case (Assume(pred1, pred2), _) => assume(and(pred1, pred2), body)
    case (_, Assume(pred2, body)) => assume(and(pred, pred2), body)
    case (BooleanLiteral(true), body) => body
    case _ => Assume(pred, body)
  }

  /** $encodingof simplified `... + ...` (plus).
    * @see [[Expressions.Plus Plus]]
    */
  def plus(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (IntegerLiteral(bi), _) if bi == 0 => rhs
    case (_, IntegerLiteral(bi)) if bi == 0 => lhs
    case (bv: BVLiteral, _) if bv.toBigInt == 0 => rhs
    case (_, bv: BVLiteral) if bv.toBigInt == 0 => lhs
    case (FractionLiteral(n, d), _) if n == 0 => rhs
    case (_, FractionLiteral(n, d)) if n == 0 => lhs
    case _ => Plus(lhs, rhs)
  }

  /** $encodingof simplified `... - ...` (minus).
    * @see [[Expressions.Minus Minus]]
    */
  def minus(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (_, IntegerLiteral(bi)) if bi == 0 => lhs
    case (_, bv: BVLiteral) if bv.toBigInt == 0 => lhs
    case (IntegerLiteral(bi), _) if bi == 0 => UMinus(rhs)
    case _ => Minus(lhs, rhs)
  }

  def uminus(e: Expr): Expr = e match {
    case IntegerLiteral(bi) if bi == 0 => e
    case bv: BVLiteral if bv.toBigInt == 0 => e
    case IntegerLiteral(bi) if bi < 0 => IntegerLiteral(-bi)
    case _ => UMinus(e)
  }

  /** $encodingof simplified `... * ...` (times).
    * @see [[Expressions.Times Times]]
    */
  def times(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (IntegerLiteral(bi), _) if bi == 1 => rhs
    case (_, IntegerLiteral(bi)) if bi == 1 => lhs
    case (IntegerLiteral(bi), _) if bi == 0 => IntegerLiteral(0)
    case (_, IntegerLiteral(bi)) if bi == 0 => IntegerLiteral(0)
    case (bv: BVLiteral, _) if bv.toBigInt == 1 => rhs
    case (_, bv: BVLiteral) if bv.toBigInt == 1 => lhs
    case (bv: BVLiteral, _) if bv.toBigInt == 0 => lhs
    case (_, bv: BVLiteral) if bv.toBigInt == 0 => rhs
    case _ => Times(lhs, rhs)
  }
}
