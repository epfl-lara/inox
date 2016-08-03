/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

/** Simplifies variable ids in scope */
trait ScopeSimplifier extends Transformer {
  import trees._
  case class Scope(inScope: Set[ValDef] = Set(), oldToNew: Map[ValDef, ValDef] = Map(), funDefs: Map[Identifier, Identifier] = Map()) {

    def register(oldNew: (ValDef, ValDef)): Scope = {
      val newId = oldNew._2
      copy(inScope = inScope + newId, oldToNew = oldToNew + oldNew)
    }

    def register(oldNews: Seq[(ValDef, ValDef)]): Scope = {
      (this /: oldNews){ case (oldScope, oldNew) => oldScope.register(oldNew) }
    }

    def registerFunDef(oldNew: (Identifier, Identifier)): Scope = {
      copy(funDefs = funDefs + oldNew)
    }
  }

  protected def genId(vd: ValDef, scope: Scope): ValDef = {
    val ValDef(id, tp) = vd
    val existCount = scope.inScope.count(_.id.name == id.name)

    ValDef(FreshIdentifier.forceId(id.name, existCount, existCount >= 1), tp)
  }

  protected def rec(e: Expr, scope: Scope): Expr = e match {
    case Let(i, e, b) =>
      val si = genId(i, scope)
      val se = rec(e, scope)
      val sb = rec(b, scope.register(i -> si))
      Let(si, se, sb)

    case MatchExpr(scrut, cases) =>
      val rs = rec(scrut, scope)

      def trPattern(p: Pattern, scope: Scope): (Pattern, Scope) = {
        val (newBinder, newScope) = p.binder match {
          case Some(id) =>
            val newId = genId(id, scope)
            val newScope = scope.register(id -> newId)
            (Some(newId), newScope)
          case None =>
            (None, scope)
        }

        var curScope = newScope
        val newSubPatterns = for (sp <- p.subPatterns) yield {
          val (subPattern, subScope) = trPattern(sp, curScope)
          curScope = subScope
          subPattern
        }

        val newPattern = p match {
          case InstanceOfPattern(b, ctd) =>
            InstanceOfPattern(newBinder, ctd)
          case WildcardPattern(b) =>
            WildcardPattern(newBinder)
          case CaseClassPattern(b, ccd, sub) =>
            CaseClassPattern(newBinder, ccd, newSubPatterns)
          case TuplePattern(b, sub) =>
            TuplePattern(newBinder, newSubPatterns)
          case UnapplyPattern(b, fd, obj, sub) =>
            UnapplyPattern(newBinder, fd, obj, newSubPatterns)
          case LiteralPattern(_, lit) =>
            LiteralPattern(newBinder, lit)
        }

        (newPattern, curScope)
      }

      MatchExpr(rs, cases.map { c =>
        val (newP, newScope) = trPattern(c.pattern, scope)
        MatchCase(newP, c.optGuard map {rec(_, newScope)}, rec(c.rhs, newScope))
      })

    case v: Variable =>
      val vd = v.toVal
      scope.oldToNew.getOrElse(vd, vd).toVariable

    // This only makes sense if we have Let-Defs at some point
    case FunctionInvocation(id, tps, args) =>
      val newFd = scope.funDefs.getOrElse(id, id)
      val newArgs = args.map(rec(_, scope))

      FunctionInvocation(newFd, tps, newArgs)

    case Operator(es, builder) =>
      builder(es.map(rec(_, scope)))

    case _ =>
      sys.error("Expression "+e+" ["+e.getClass+"] is not extractable")
  }

}
