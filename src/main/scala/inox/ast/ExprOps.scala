/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

/** Provides functions to manipulate [[Expressions.Expr]].
  *
  * This object provides a few generic operations on Leon expressions,
  * as well as some common operations.
  *
  * The generic operations lets you apply operations on a whole tree
  * expression. You can look at:
  *   - [[GenTreeOps.fold foldRight]]
  *   - [[GenTreeOps.preTraversal preTraversal]]
  *   - [[GenTreeOps.postTraversal postTraversal]]
  *   - [[GenTreeOps.preMap preMap]]
  *   - [[GenTreeOps.postMap postMap]]
  *   - [[GenTreeOps.genericTransform genericTransform]]
  *
  * These operations usually take a higher order function that gets applied to the
  * expression tree in some strategy. They provide an expressive way to build complex
  * operations on Leon expressions.
  *
  */
trait ExprOps extends GenTreeOps {
  protected val trees: Trees
  val sourceTrees: trees.type = trees
  val targetTrees: trees.type = trees

  import trees._

  type Source = Expr
  type Target = Expr

  lazy val Deconstructor = Operator

  /** Replaces bottom-up variables by looking up for them in a map */
  def replaceFromSymbols[V <: VariableSymbol](substs: Map[V, Expr], expr: Expr)(implicit ev: VariableConverter[V]): Expr = {
    postMap {
      case v: Variable => substs.get(v.to[V])
      case _ => None
    } (expr)
  }

  /** Replaces bottom-up variables by looking them up in a map from [[ValDef]] to expressions */
  def replaceFromSymbols(substs: Map[ValDef, Expr], expr: Expr): Expr = postMap {
    case v: Variable => substs.get(v.toVal)
    case _ => None
  } (expr)

  protected class VariableExtractor {
    def unapply(e: Expr): Option[(Set[Variable], Set[Variable])] = e match {
      case v: Variable => Some((Set(v), Set.empty))
      case Let(vd, _, _) => Some((Set.empty, Set(vd.toVariable)))
      case Lambda(args, _) => Some((Set.empty, args.map(_.toVariable).toSet))
      case Forall(args, _) => Some((Set.empty, args.map(_.toVariable).toSet))
      case Choose(res, _) => Some((Set.empty, Set(res.toVariable)))
      case _ => Some((Set.empty, Set.empty))
    }
  }

  protected val VariableExtractor = new VariableExtractor

  /** Returns the set of free variables in an expression */
  def variablesOf(expr: Expr): Set[Variable] = {
    fold[Set[Variable]] { case (e, subs) =>
      val subvs = subs.flatten.toSet
      val VariableExtractor(add, remove) = e
      subvs ++ add -- remove
    }(expr)
  }

  /** Returns true if the expression contains a function call */
  def containsFunctionCalls(expr: Expr): Boolean = {
    exists{
      case _: FunctionInvocation => true
      case _ => false
    }(expr)
  }

  /** Returns all Function calls found in the expression */
  def functionCallsOf(expr: Expr): Set[FunctionInvocation] = {
    collect[FunctionInvocation] {
      case f: FunctionInvocation => Set(f)
      case _ => Set()
    }(expr)
  }

  /** Returns '''true''' if the formula is Ground,
    * which means that it does not contain any variables
    * ([[purescala.ExprOps#variablesOf]] e is empty)
    */
  def isGround(e: Expr): Boolean = variablesOf(e).isEmpty

  /** Returns '''true''' if the formula is simple,
    * which means that it requires no special encoding for an
    * unrolling solver. See implementation for what this means exactly.
    */
  def isSimple(e: Expr): Boolean = !exists {
    case (_: Assume) | (_: Forall) | (_: Lambda) | (_: Choose) |
         (_: FunctionInvocation) | (_: Application) => true
    case _ => false
  } (e)

  /* Checks if a given expression is 'real' and does not contain generic
   * values. */
  def isRealExpr(v: Expr): Boolean = {
    !exists {
      case gv: GenericValue => true
      case _ => false
    }(v)
  }

  def preTraversalWithParent(f: (Expr, Option[Tree]) => Unit, initParent: Option[Tree] = None)(e: Expr): Unit = {
    val rec = preTraversalWithParent(f, Some(e)) _

    f(e, initParent)

    val Operator(es, _) = e
    es foreach rec
  }

  /** Simple, local optimization on string */
  def simplifyString(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = (expr match {
      case StringConcat(StringLiteral(""), b) => b
      case StringConcat(b, StringLiteral("")) => b
      case StringConcat(StringLiteral(a), StringLiteral(b)) => StringLiteral(a + b)
      case StringLength(StringLiteral(a)) => IntLiteral(a.length)
      case SubString(StringLiteral(a), IntLiteral(start), IntLiteral(end)) =>
        StringLiteral(a.substring(start.toInt, end.toInt))
      case _ => expr
    }).copiedFrom(expr)

    utils.fixpoint(simplePostTransform(simplify0))(expr)
  }

  /** Simple, local simplification on arithmetic
    *
    * You should not assume anything smarter than some constant folding and
    * simple cancellation. To avoid infinite cycle we only apply simplification
    * that reduce the size of the tree. The only guarantee from this function is
    * to not augment the size of the expression and to be sound.
    */
  def simplifyArithmetic(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = (expr match {
      case Plus(IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 + i2)
      case Plus(IntegerLiteral(zero), e) if zero == BigInt(0) => e
      case Plus(e, IntegerLiteral(zero)) if zero == BigInt(0) => e
      case Plus(e1, UMinus(e2)) => Minus(e1, e2)
      case Plus(Plus(e, IntegerLiteral(i1)), IntegerLiteral(i2)) => Plus(e, IntegerLiteral(i1+i2))
      case Plus(Plus(IntegerLiteral(i1), e), IntegerLiteral(i2)) => Plus(IntegerLiteral(i1+i2), e)

      case Minus(e, IntegerLiteral(zero)) if zero == BigInt(0) => e
      case Minus(IntegerLiteral(zero), e) if zero == BigInt(0) => UMinus(e)
      case Minus(IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 - i2)
      case Minus(e1, UMinus(e2)) => Plus(e1, e2)
      case Minus(e1, Minus(UMinus(e2), e3)) => Plus(e1, Plus(e2, e3))

      case UMinus(IntegerLiteral(x)) => IntegerLiteral(-x)
      case UMinus(UMinus(x)) => x
      case UMinus(Plus(UMinus(e1), e2)) => Plus(e1, UMinus(e2))
      case UMinus(Minus(e1, e2)) => Minus(e2, e1)

      case Times(IntegerLiteral(i1), IntegerLiteral(i2)) => IntegerLiteral(i1 * i2)
      case Times(IntegerLiteral(one), e) if one == BigInt(1) => e
      case Times(IntegerLiteral(mone), e) if mone == BigInt(-1) => UMinus(e)
      case Times(e, IntegerLiteral(one)) if one == BigInt(1) => e
      case Times(IntegerLiteral(zero), _) if zero == BigInt(0) => IntegerLiteral(0)
      case Times(_, IntegerLiteral(zero)) if zero == BigInt(0) => IntegerLiteral(0)
      case Times(IntegerLiteral(i1), Times(IntegerLiteral(i2), t)) => Times(IntegerLiteral(i1*i2), t)
      case Times(IntegerLiteral(i1), Times(t, IntegerLiteral(i2))) => Times(IntegerLiteral(i1*i2), t)
      case Times(IntegerLiteral(i), UMinus(e)) => Times(IntegerLiteral(-i), e)
      case Times(UMinus(e), IntegerLiteral(i)) => Times(e, IntegerLiteral(-i))
      case Times(IntegerLiteral(i1), Division(e, IntegerLiteral(i2))) if i2 != BigInt(0) && i1 % i2 == BigInt(0) =>
        Times(IntegerLiteral(i1/i2), e)

      case Division(IntegerLiteral(i1), IntegerLiteral(i2)) if i2 != BigInt(0) => IntegerLiteral(i1 / i2)
      case Division(e, IntegerLiteral(one)) if one == BigInt(1) => e

      //here we put more expensive rules
      //btw, I know those are not the most general rules, but they lead to good optimizations :)
      case Plus(UMinus(Plus(e1, e2)), e3) if e1 == e3 => UMinus(e2)
      case Plus(UMinus(Plus(e1, e2)), e3) if e2 == e3 => UMinus(e1)
      case Minus(e1, e2) if e1 == e2 => IntegerLiteral(0)
      case Minus(Plus(e1, e2), Plus(e3, e4)) if e1 == e4 && e2 == e3 => IntegerLiteral(0)
      case Minus(Plus(e1, e2), Plus(Plus(e3, e4), e5)) if e1 == e4 && e2 == e3 => UMinus(e5)

      case StringConcat(StringLiteral(""), a) => a
      case StringConcat(a, StringLiteral("")) => a
      case StringConcat(StringLiteral(a), StringLiteral(b)) => StringLiteral(a+b)
      case StringConcat(StringLiteral(a), StringConcat(StringLiteral(b), c)) => StringConcat(StringLiteral(a+b), c)
      case StringConcat(StringConcat(c, StringLiteral(a)), StringLiteral(b)) => StringConcat(c, StringLiteral(a+b))
      case StringConcat(a, StringConcat(b, c)) => StringConcat(StringConcat(a, b), c)
      //default
      case e => e
    }).copiedFrom(expr)

    utils.fixpoint(simplePostTransform(simplify0))(expr)
  }

  /**
    * Some helper methods for FractionLiterals
    */
  def normalizeFraction(fl: FractionLiteral) = {
    val FractionLiteral(num, denom) = fl
    val modNum = if (num < 0) -num else num
    val modDenom = if (denom < 0) -denom else denom
    val divisor = modNum.gcd(modDenom)
    val simpNum = num / divisor
    val simpDenom = denom / divisor
    if (simpDenom < 0)
      FractionLiteral(-simpNum, -simpDenom)
    else
      FractionLiteral(simpNum, simpDenom)
  }

  val realzero = FractionLiteral(0, 1)
  def floor(fl: FractionLiteral): FractionLiteral = {
    val FractionLiteral(n, d) = normalizeFraction(fl)
    if (d == 0) throw new IllegalStateException("denominator zero")
    if (n == 0) realzero
    else if (n > 0) {
      //perform integer division
      FractionLiteral(n / d, 1)
    } else {
      //here the number is negative
      if (n % d == 0)
        FractionLiteral(n / d, 1)
      else {
        //perform integer division and subtract 1
        FractionLiteral(n / d - 1, 1)
      }
    }
  }
}
