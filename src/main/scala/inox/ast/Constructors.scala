/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

/** Provides constructors for [[Expressions]].
  *
  * The constructors implement some logic to simplify the tree and
  * potentially use a different expression node if one is more suited.
  * @define encodingof Encoding of
  *  */
trait Constructors {
  protected val trees: Trees
  import trees._
  import trees.exprOps._
  protected implicit val symbols: Symbols
  import symbols._

  /** If `isTuple`:
    * `tupleSelect(tupleWrap(Seq(Tuple(x,y))),1) -> x`
    * `tupleSelect(tupleExpr,1) -> tupleExpr._1`
    * If not `isTuple` (usually used only in the case of a tuple of arity 1)
    * `tupleSelect(tupleWrap(Seq(Tuple(x,y))),1) -> Tuple(x,y)`.
    * @see [[Expressions.TupleSelect TupleSelect]]
    */
  def tupleSelect(t: Expr, index: Int, isTuple: Boolean): Expr = t match {
    case Tuple(es) if isTuple => es(index-1)
    case _ if t.getType.isInstanceOf[TupleType] && isTuple =>
      TupleSelect(t, index)
    case other if !isTuple => other
    case _ =>
      sys.error(s"Calling tupleSelect on non-tuple $t")
  }

  /** Simplifies the construct `TupleSelect(expr, index, originalSize > 1)`
    * @param originalSize The arity of the tuple. If less or equal to 1, the whole expression is returned.
    * @see [[Expressions.TupleSelect TupleSelect]]
    */
  def tupleSelect(t: Expr, index: Int, originalSize: Int): Expr = tupleSelect(t, index, originalSize > 1)

  /** $encodingof ``val id = e; bd``, and returns `bd` if the identifier is not bound in `bd`.
    * @see [[Expressions.Let Let]]
    */
  def let(vd: ValDef, e: Expr, bd: Expr) = {
    if (exprOps.variablesOf(bd) contains vd.toVariable)
      Let(vd, e, bd)
    else bd
  }

  /** Wraps the sequence of expressions as a tuple. If the sequence contains a single expression, it is returned instead.
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
  def tupleTypeWrap(tps: Seq[Type]) = tps match {
    case Seq() => UnitType
    case Seq(elem) => elem
    case more => TupleType(more)
  }

  /** Instantiates the type parameters of the function according to argument types
    * @return A [[Expressions.FunctionInvocation FunctionInvocation]] if it type checks, else throws an error.
    * @see [[Expressions.FunctionInvocation]]
    */
  def functionInvocation(fd: FunDef, args: Seq[Expr]) = {
    require(fd.params.length == args.length, "Invoking function with incorrect number of arguments")

    val formalType = tupleTypeWrap(fd.params map { _.getType })
    val actualType = tupleTypeWrap(args map { _.getType })

    symbols.canBeSupertypeOf(formalType, actualType) match {
      case Some(tmap) =>
        FunctionInvocation(fd.id, fd.tparams map { tpd => tmap.getOrElse(tpd.tp, tpd.tp) }, args)
      case None => throw FatalError(s"$args:$actualType cannot be a subtype of $formalType!")
    }
  }

  /** Instantiates the type parameters of the ADT constructor according to argument types
    * @return A [[Expressions.ADT ADT]] if it type checks, else throws an error
    * @see [[Expressions.ADT]]
    */
  def adtConstruction(adt: ADTConstructor, args: Seq[Expr]) = {
    require(adt.fields.length == args.length, "Constructing adt with incorrect number of arguments")

    val formalType = tupleTypeWrap(adt.fields.map(_.tpe))
    val actualType = tupleTypeWrap(args.map(_.getType))

    symbols.canBeSupertypeOf(formalType, actualType) match {
      case Some(tmap) => ADT(instantiateType(adt.typed.toType, tmap).asInstanceOf[ADTType], args)
      case None => throw FatalError(s"$args:$actualType cannot be a subtype of $formalType!")
    }
  }

  /** Simplifies the provided case class selector.
    * @see [[Expressions.ADTSelector ADTSelector]]
    */
  def adtSelector(adt: Expr, selector: Identifier): Expr = {
    adt match {
      case a @ ADT(tp, fields) if !tp.getADT.hasInvariant =>
        fields(tp.getADT.toConstructor.definition.selectorID2Index(selector))
      case _ =>
        ADTSelector(adt, selector)
    }
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

    simpler match {
      case Seq()  => BooleanLiteral(true)
      case Seq(x) => x
      case _      => And(simpler)
    }
  }

  /** $encodingof `&&`-expressions with arbitrary number of operands as a sequence, and simplified.
    * @see [[Expressions.And And]]
    */
  def andJoin(es: Seq[Expr]) = and(es :_*)

  /** $encodingof `||`-expressions with arbitrary number of operands, and simplified.
    * @see [[Expressions.Or Or]]
    */
  def or(exprs: Expr*): Expr = {
    val flat = exprs.flatMap {
      case Or(es) => es
      case o => Seq(o)
    }

    var stop = false
    val simpler = for(e <- flat if !stop && e != BooleanLiteral(false)) yield {
      if(e == BooleanLiteral(true)) stop = true
      e
    }

    simpler match {
      case Seq()  => BooleanLiteral(false)
      case Seq(x) => x
      case _      => Or(simpler)
    }
  }

  /** $encodingof `||`-expressions with arbitrary number of operands as a sequence, and simplified.
    * @see [[Expressions.Or Or]]
    */
  def orJoin(es: Seq[Expr]) = or(es :_*)

  /** $encodingof simplified `!`-expressions .
    * @see [[Expressions.Not Not]]
    */
  def not(e: Expr): Expr = negate(e)

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
    } else  {
      Equals(a, b)
    }
  }

  /** $encodingof simplified `fn(realArgs)` (function application).
    * Transforms
    * {{{ ((x: A, y: B) => g(x, y))(c, d) }}}
    * into
    * {{{val x0 = c
    * val y0 = d
    * g(x0, y0)}}}
    * and further simplifies it.
    * @see [[Expressions.Lambda Lambda]]
    * @see [[Expressions.Application Application]]
    */
  def application(fn: Expr, realArgs: Seq[Expr]) = fn match {
     case Lambda(formalArgs, body) =>
      assert(realArgs.size == formalArgs.size, "Invoking lambda with incorrect number of arguments")

      var defs: Seq[(ValDef, Expr)] = Seq()

      val subst = formalArgs.zip(realArgs).map {
        case (vd, to:Variable) =>
          vd -> to
        case (vd, e) =>
          val fresh = vd.freshen
          defs :+= (fresh -> e)
          vd -> fresh.toVariable
      }.toMap

      defs.foldRight(exprOps.replaceFromSymbols(subst, body)) {
        case ((vd, bd), body) => let(vd, bd, body)
      }

    case _ =>
      Application(fn, realArgs)
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

  /** $encodingof simplified `forall(args, body)` (universal quantification).
    * @see [[Expressions.Forall Forall]]
    */
  def forall(args: Seq[ValDef], body: Expr): Expr = body match {
    case BooleanLiteral(true) => BooleanLiteral(true)
    case _ =>
      val vars = variablesOf(body)
      Forall(args.filter(vd => vars(vd.toVariable)), body)
  }

  /** $encodingof simplified `... + ...` (plus).
    * @see [[Expressions.Plus Plus]]
    */
  def plus(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (IntegerLiteral(bi), _) if bi == 0 => rhs
    case (_, IntegerLiteral(bi)) if bi == 0 => lhs
    case (IntLiteral(0), _) => rhs
    case (_, IntLiteral(0)) => lhs
    case (FractionLiteral(n, d), _) if n == 0 => rhs
    case (_, FractionLiteral(n, d)) if n == 0 => lhs
    case _ => Plus(lhs, rhs)
  }

  /** $encodingof simplified `... - ...` (minus).
    * @see [[Expressions.Minus Minus]]
    */
  def minus(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (_, IntegerLiteral(bi)) if bi == 0 => lhs
    case (_, IntLiteral(0)) => lhs
    case (IntegerLiteral(bi), _) if bi == 0 => UMinus(rhs)
    case _ => Minus(lhs, rhs)
  }

  def uminus(e: Expr): Expr = e match {
    case IntegerLiteral(bi) if bi == 0 => e
    case IntLiteral(0) => e
    case IntegerLiteral(bi) if bi < 0 => IntegerLiteral(-bi)
    case UMinus(i) if i.getType == IntegerType => i
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
    case (IntLiteral(1), _) => rhs
    case (_, IntLiteral(1)) => lhs
    case (IntLiteral(0), _) => IntLiteral(0)
    case (_, IntLiteral(0)) => IntLiteral(0)
    case _ => Times(lhs, rhs)
  }

  /** $encodingof expr.asInstanceOf[tpe], returns `expr` if it already is of type `tpe`.  */
  def asInstOf(expr: Expr, tpe: ADTType) = {
    if (symbols.isSubtypeOf(expr.getType, tpe)) {
      expr
    } else {
      AsInstanceOf(expr, tpe)
    }
  }

  def isInstOf(expr: Expr, tpe: ADTType) = {
    if (symbols.isSubtypeOf(expr.getType, tpe)) {
      BooleanLiteral(true)
    } else {
      IsInstanceOf(expr, tpe)
    }
  }
}
