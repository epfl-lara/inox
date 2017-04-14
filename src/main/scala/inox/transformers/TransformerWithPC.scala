/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

/** A [[Transformer]] which uses path conditions as environment */
trait TransformerWithPC extends Transformer {
  val symbols: trees.Symbols
  import trees._
  import symbols._

  type Env <: PathLike[Env]

  protected def rec(e: Expr, env: Env): Expr = e match {
    case Let(i, v, b) =>
      val se = rec(v, env)
      val sb = rec(b, env withBinding (i -> se))
      Let(i, se, sb).copiedFrom(e)

    case Assume(pred, body) =>
      val sp = rec(pred, env)
      val sb = rec(body, env withCond sp)
      Assume(sp, sb).copiedFrom(e)

    case IfExpr(cond, thenn, elze) =>
      val rc = rec(cond, env)
      IfExpr(rc, rec(thenn, env withCond rc), rec(elze, env withCond Not(rc))).copiedFrom(e)

    case And(es) =>
      var soFar = env
      andJoin(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = soFar withCond se
        se
      }).copiedFrom(e)

    case Or(es) =>
      var soFar = env
      orJoin(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = soFar withCond Not(se)
        se
      }).copiedFrom(e)

    case i @ Implies(lhs, rhs) =>
      val rc = rec(lhs, env)
      Implies(rc, rec(rhs, env withCond rc)).copiedFrom(i)

    case o @ Operator(es, builder) =>
      builder(es.map(rec(_, env))).copiedFrom(o)
  }
}
