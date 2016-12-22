/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

/** A [[Transformer]] which uses path conditions as environment */
trait TransformerWithPC extends Transformer {
  val symbols: trees.Symbols
  import trees._
  import symbols._

  type Env = Path

  protected def rec(e: Expr, path: Path): Expr = e match {
    case Let(i, v, b) =>
      val se = rec(v, path)
      val sb = rec(b, path withBinding (i -> se))
      Let(i, se, sb).copiedFrom(e)

    case Assume(pred, body) =>
      val sp = rec(pred, path)
      val sb = rec(body, path withCond sp)
      Assume(sp, sb).copiedFrom(e)

    case IfExpr(cond, thenn, elze) =>
      val rc = rec(cond, path)
      IfExpr(rc, rec(thenn, path withCond rc), rec(elze, path withCond Not(rc))).copiedFrom(e)

    case And(es) =>
      var soFar = path
      andJoin(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = soFar withCond se
        se
      }).copiedFrom(e)

    case Or(es) =>
      var soFar = path
      orJoin(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = soFar withCond Not(se)
        se
      }).copiedFrom(e)

    case i @ Implies(lhs, rhs) =>
      val rc = rec(lhs, path)
      Implies(rc, rec(rhs, path withCond rc)).copiedFrom(i)

    case o @ Operator(es, builder) =>
      builder(es.map(rec(_, path))).copiedFrom(o)
  }
}
