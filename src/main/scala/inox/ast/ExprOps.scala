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
  import trees._

  type SubTree = Expr

  val Deconstructor = Operator

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

  /** Returns the set of free variables in an expression */
  def variablesOf(expr: Expr): Set[Variable] = {
    fold[Set[Variable]] {
      case (e, subs) =>
        val subvs = subs.flatten.toSet
        e match {
          case v: Variable => subvs + v
          case Let(vd, _, _) => subvs - vd.toVariable
          case MatchExpr(_, cses) => subvs -- cses.flatMap(_.pattern.binders).map(_.toVariable)
          case Lambda(args, _) => subvs -- args.map(_.toVariable)
          case Forall(args, _) => subvs -- args.map(_.toVariable)
          case _ => subvs
        }
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
    case (_: Assert) | (_: Ensuring) |
         (_: Forall) | (_: Lambda) |
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

  override def formulaSize(e: Expr): Int = e match {
    case ml: MatchExpr =>
      super.formulaSize(e) + ml.cases.map(cs => patternOps.formulaSize(cs.pattern)).sum
    case _ =>
      super.formulaSize(e)
  }

  /** Returns if this expression behaves as a purely functional construct,
    * i.e. always returns the same value (for the same environment) and has no side-effects
    */
  def isPurelyFunctional(e: Expr): Boolean = !exists {
    case _ : Error => true
    case _ => false
  }(e)

  /** Extracts the body without its specification
    *
    * [[Expressions.Expr]] trees contain its specifications as part of certain nodes.
    * This function helps extracting only the body part of an expression
    *
    * @return An option type with the resulting expression if not [[Expressions.NoTree]]
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withoutSpec(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)                    => withoutSpec(b).map(Let(i, e, _))
    case Require(pre, b)                 => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Require(pre, b), post) => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(b, post)               => Option(b).filterNot(_.isInstanceOf[NoTree])
    case b                               => Option(b).filterNot(_.isInstanceOf[NoTree])
  }

  /** Returns the precondition of an expression wrapped in Option */
  def preconditionOf(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)                 => preconditionOf(b).map(Let(i, e, _).copiedFrom(expr))
    case Require(pre, _)              => Some(pre)
    case Ensuring(Require(pre, _), _) => Some(pre)
    case b                            => None
  }

  /** Returns the postcondition of an expression wrapped in Option */
  def postconditionOf(expr: Expr): Option[Lambda] = expr match {
    case Let(i, e, b)              => postconditionOf(b).map(l => l.copy(body = Let(i, e, l.body)).copiedFrom(expr))
    case Ensuring(_, post: Lambda) => Some(post)
    case _                         => None
  }

  /** Returns a tuple of precondition, the raw body and the postcondition of an expression */
  def breakDownSpecs(e: Expr) = (preconditionOf(e), withoutSpec(e), postconditionOf(e))

  def preTraversalWithParent(f: (Expr, Option[Tree]) => Unit, initParent: Option[Tree] = None)(e: Expr): Unit = {
    val rec = preTraversalWithParent(f, Some(e)) _

    f(e, initParent)

    val Deconstructor(es, _) = e
    es foreach rec
  }
}
