/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

import utils._

trait SimplifierWithPath extends SimplifierWithPC {
  import trees._
  import symbols.{given, _}

  class Env private(
    private val conditions: Set[Expr],
    private val exprSubst: Map[Variable, Expr],
    override val recorder: Recorder = null
  ) extends PathLike[Env] with SolvingPath {

    override def withBinding(p: (ValDef, Expr)): Env = p match {
      case (vd, expr @ (_: ADT | _: Tuple | _: Lambda)) =>
        new Env(conditions, exprSubst + (vd.toVariable -> expr), recorder)
      case (vd, v: Variable) =>
        val exp = expand(v)
        if (v != exp) new Env(conditions, exprSubst + (vd.toVariable -> exp), recorder)
        else this
      case _ => this
    }

    override def withBound(vd: ValDef): Env = this // We don't need to track such bounds.

    override def withCond(cond: Expr): Env = new Env(conditions + cond, exprSubst, recorder)

    override def negate: Env = new Env(Set(not(and(conditions.toSeq*))), exprSubst, recorder)

    override def merge(that: Env): Env =
      new Env(conditions ++ that.conditions, exprSubst ++ that.exprSubst, recorder)

    override def expand(expr: Expr): Expr = expr match {
      case v: Variable => exprSubst.getOrElse(v, v)
      case _ => expr
    }

    override def implies(expr: Expr): Boolean = conditions contains expr

    override def toString: String = conditions.toString
  }

  object Env extends PathProvider[Env] {
    def empty = new Env(Set(), Map())

    /** The empty path of a simplification that records its steps in `recorder`, unless it is
      * `null`. */
    def recording(recorder: Recorder): Env =
      if (recorder eq null) empty else new Env(Set(), Map(), recorder)
  }

  override def initEnv = Env.empty
}
