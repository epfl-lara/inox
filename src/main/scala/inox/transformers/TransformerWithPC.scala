/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

/** A [[Transformer]] that uses the path condition _before transformation_ as environment */
trait TransformerWithPC extends Transformer {
  type Env <: s.PathLike[Env]

  override def transform(e: s.Expr, env: Env): t.Expr = e match {
    case s.Let(i, v, b) =>
      t.Let(transform(i, env), transform(v, env), transform(b, env withBinding (i -> v))).copiedFrom(e)

    case s.Lambda(params, b) =>
      val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
        case ((sparams, env), vd) => (sparams :+ transform(vd, env), env withBound vd)
      }
      t.Lambda(sparams, transform(b, senv)).copiedFrom(e)

    case s.Forall(params, b) =>
      val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
        case ((sparams, env), vd) => (sparams :+ transform(vd, env), env withBound vd)
      }
      t.Forall(sparams, transform(b, senv)).copiedFrom(e)

    case s.Choose(res, p) =>
      t.Choose(transform(res, env), transform(p, env withBound res)).copiedFrom(e)

    case s.Assume(pred, body) =>
      t.Assume(transform(pred, env), transform(body, env withCond pred)).copiedFrom(e)

    case s.IfExpr(cond, thenn, elze) =>
      t.IfExpr(
        transform(cond, env),
        transform(thenn, env withCond cond),
        transform(elze, env withCond s.Not(cond).copiedFrom(cond))
      ).copiedFrom(e)

    case s.And(es) =>
      t.And(es.foldLeft((env, List[t.Expr]())) { case ((soFar, res), e) =>
        (soFar withCond e, res :+ transform(e, soFar))
      }._2).copiedFrom(e)

    case s.Or(es) =>
      t.Or(es.foldLeft((env, List[t.Expr]())) { case ((soFar, res), e) =>
        (soFar withCond s.Not(e).copiedFrom(e), res :+ transform(e, soFar))
      }._2).copiedFrom(e)

    case s.Implies(lhs, rhs) =>
      t.Implies(transform(lhs, env), transform(rhs, env withCond lhs)).copiedFrom(e)

    case _ => super.transform(e, env)
  }

  override def transform(tpe: s.Type, env: Env): t.Type = tpe match {
    case s.RefinementType(vd, prop) =>
      t.RefinementType(transform(vd, env), transform(prop, env withBound vd)).copiedFrom(tpe)

    case s.PiType(params, to) =>
      val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
        case ((sparams, env), vd) => (sparams :+ transform(vd, env), env withBound vd)
      }
      t.PiType(sparams, transform(to, senv)).copiedFrom(tpe)

    case s.SigmaType(params, to) =>
      val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
        case ((sparams, env), vd) => (sparams :+ transform(vd, env), env withBound vd)
      }
      t.SigmaType(sparams, transform(to, senv)).copiedFrom(tpe)

    case _ => super.transform(tpe, env)
  }
}

