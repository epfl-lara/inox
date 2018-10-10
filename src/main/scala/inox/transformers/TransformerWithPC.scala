/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

/** A [[Transformer]] that uses the path condition _before transformation_ as environment */
trait TransformerWithPrePC extends Transformer {

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
      var soFar = env
      t.andJoin(for(e <- es) yield {
        val se = transform(e, soFar)
        soFar = soFar withCond e
        se
      }).copiedFrom(e)

    case s.Or(es) =>
      var soFar = env
      t.orJoin(for(e <- es) yield {
        val se = transform(e, soFar)
        soFar = soFar withCond s.Not(e).copiedFrom(e)
        se
      }).copiedFrom(e)

    case s.Implies(lhs, rhs) =>
      t.Implies(transform(lhs, env), transform(rhs, env withCond lhs)).copiedFrom(e)

    case _ => super.transform(e, env)
  }
}

/** A [[Transformer]] that uses the path condition _after transformation_ as environment */
trait TransformerWithPostPC extends Transformer {

  type Env <: t.PathLike[Env]

  override def transform(e: s.Expr, env: Env): t.Expr = e match {
    case s.Let(i, v, b) =>
      val si = transform(i, env)
      val se = transform(v, env)
      val sb = transform(b, env withBinding (si -> se))
      t.Let(si, se, sb).copiedFrom(e)

    case s.Lambda(params, b) =>
      val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
        case ((sparams, env), vd) =>
          val svd = transform(vd, env)
          (sparams :+ svd, env withBound svd)
      }
      val sb = transform(b, senv)
      t.Lambda(sparams, sb).copiedFrom(e)

    case s.Forall(params, b) =>
      val (sparams, senv) = params.foldLeft((Seq[t.ValDef](), env)) {
        case ((sparams, env), vd) =>
          val svd = transform(vd, env)
          (sparams :+ svd, env withBound svd)
      }
      val sb = transform(b, senv)
      t.Forall(sparams, sb).copiedFrom(e)

    case s.Choose(res, p) =>
      val sres = transform(res, env)
      val sp = transform(p, env withBound sres)
      t.Choose(sres, sp).copiedFrom(e)

    case s.Assume(pred, body) =>
      val sp = transform(pred, env)
      val sb = transform(body, env withCond sp)
      t.Assume(sp, sb).copiedFrom(e)

    case s.IfExpr(cond, thenn, elze) =>
      val rc = transform(cond, env)
      t.IfExpr(
        rc,
        transform(thenn, env withCond rc),
        transform(elze, env withCond t.Not(rc).copiedFrom(rc))
      ).copiedFrom(e)

    case s.And(es) =>
      var soFar = env
      t.andJoin(for(e <- es) yield {
        val se = transform(e, soFar)
        soFar = soFar withCond se
        se
      }).copiedFrom(e)

    case s.Or(es) =>
      var soFar = env
      t.orJoin(for(e <- es) yield {
        val se = transform(e, soFar)
        soFar = soFar withCond t.Not(se).copiedFrom(se)
        se
      }).copiedFrom(e)

    case s.Implies(lhs, rhs) =>
      val rc = transform(lhs, env)
      t.Implies(rc, transform(rhs, env withCond rc)).copiedFrom(e)

    case _ => super.transform(e, env)
  }
}

