/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

import utils._

trait SimplifierWithPath extends SimplifierWithPC {
  import trees._
  import symbols.{given, _}

  /** A path of conditions and bindings, with what a simplification is given for the term that
    * it simplifies: the `recorder` of its steps and the `evaluator` of its ground terms, which
    * are `null` when it doesn't record and doesn't evaluate, and whether the path is `underLambda`,
    * the body of a lambda. */
  class Env private(
    private val conditions: Set[Expr],
    private val exprSubst: Map[Variable, Expr],
    override val recorder: Recorder = noRecorder,
    val evaluator: Expr => Option[Expr] = null,
    val underLambda: Boolean = false
  ) extends PathLike[Env] with SolvingPath {

    private def copy(conditions: Set[Expr] = conditions, exprSubst: Map[Variable, Expr] = exprSubst,
                     underLambda: Boolean = underLambda): Env =
      new Env(conditions, exprSubst, recorder, evaluator, underLambda)

    override def withBinding(p: (ValDef, Expr)): Env = p match {
      case (vd, expr @ (_: ADT | _: Tuple | _: Lambda)) =>
        copy(exprSubst = exprSubst + (vd.toVariable -> expr))
      case (vd, v: Variable) =>
        val exp = expand(v)
        if (v != exp) copy(exprSubst = exprSubst + (vd.toVariable -> exp))
        else this
      case _ => this
    }

    override def withBound(vd: ValDef): Env = this // We don't need to track such bounds.

    override def withCond(cond: Expr): Env = copy(conditions = conditions + cond)

    override def negate: Env = copy(conditions = Set(not(and(conditions.toSeq*))))

    override def merge(that: Env): Env =
      copy(conditions = conditions ++ that.conditions, exprSubst = exprSubst ++ that.exprSubst)

    /** This path without its evaluator. */
    def withoutEvaluator: Env =
      if (evaluator eq null) this else new Env(conditions, exprSubst, recorder, null, underLambda)

    /** This path in the body of a lambda. */
    def inLambda: Env = if (underLambda) this else copy(underLambda = true)

    override def expand(expr: Expr): Expr = expr match {
      case v: Variable => exprSubst.getOrElse(v, v)
      case _ => expr
    }

    override def implies(expr: Expr): Boolean = conditions contains expr

    override def toString: String = conditions.toString
  }

  object Env extends PathProvider[Env] {
    def empty = new Env(Set(), Map())

    /** The empty path of a simplification that records its steps in `recorder` and evaluates
      * its ground terms with `evaluator`, unless they are `null`. */
    def of(recorder: Recorder, evaluator: Expr => Option[Expr]): Env =
      new Env(Set(), Map(), recorder, evaluator)
  }

  override def initEnv = Env.empty
}
