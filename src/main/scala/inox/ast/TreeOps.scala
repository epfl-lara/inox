
package inox
package ast

trait TreeOps {
  private[ast] val trees: Trees
  import trees._

  trait TreeTransformer {
    def transform(id: Identifier, tpe: Type): (Identifier, Type) = (id, transform(tpe))

    def transform(v: Variable): Variable = {
      val (id, tpe) = transform(v.id, v.tpe)
      Variable(id, tpe).copiedFrom(v)
    }

    def transform(vd: ValDef): ValDef = {
      val (id, tpe) = transform(vd.id, vd.tpe)
      ValDef(id, tpe).copiedFrom(vd)
    }

    def transform(e: Expr): Expr = e match {
      case v: Variable => transform(v)

      case Lambda(args, body) =>
        Lambda(args map transform, transform(body)).copiedFrom(e)

      case Forall(args, body) =>
        Forall(args map transform, transform(body)).copiedFrom(e)

      case Let(vd, expr, body) =>
        Let(transform(vd), transform(expr), transform(body)).copiedFrom(e)

      case CaseClass(cct, args) =>
        CaseClass(transform(cct).asInstanceOf[ClassType], args map transform).copiedFrom(e)

      case CaseClassSelector(cct, caseClass, selector) =>
        CaseClassSelector(transform(cct).asInstanceOf[ClassType], transform(caseClass), selector).copiedFrom(e)

      case FunctionInvocation(id, tps, args) =>
        FunctionInvocation(id, tps map transform, args map transform).copiedFrom(e)

      case IsInstanceOf(expr, ct) =>
        IsInstanceOf(transform(expr), transform(ct).asInstanceOf[ClassType]).copiedFrom(e)

      case AsInstanceOf(expr, ct) => 
        AsInstanceOf(transform(expr), transform(ct).asInstanceOf[ClassType]).copiedFrom(e)

      case MatchExpr(scrutinee, cases) =>
        MatchExpr(transform(scrutinee), for (cse @ MatchCase(pattern, guard, rhs) <- cases) yield {
          MatchCase(transform(pattern), guard.map(transform), transform(rhs)).copiedFrom(cse)
        }).copiedFrom(e)

      case FiniteSet(es, tpe) =>
        FiniteSet(es map transform, transform(tpe)).copiedFrom(e)

      case FiniteBag(es, tpe) =>
        FiniteBag(es map { case (k, v) => transform(k) -> v }, transform(tpe)).copiedFrom(e)

      case FiniteMap(pairs, from, to) =>
        FiniteMap(pairs map { case (k, v) => transform(k) -> transform(v) }, transform(from), transform(to)).copiedFrom(e)

      case NoTree(tpe) =>
        NoTree(transform(tpe)).copiedFrom(e)

      case Error(tpe, desc) =>
        Error(transform(tpe), desc).copiedFrom(e)

      case Operator(es, builder) =>
        val newEs = es map transform
        if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
          builder(newEs).copiedFrom(e)
        } else {
          e
        }

      case e => e
    }

    def transform(pat: Pattern): Pattern = pat match {
      case InstanceOfPattern(binder, ct) =>
        InstanceOfPattern(binder map transform, transform(ct).asInstanceOf[ClassType]).copiedFrom(pat)

      case CaseClassPattern(binder, ct, subs) =>
        CaseClassPattern(binder map transform, transform(ct).asInstanceOf[ClassType], subs map transform).copiedFrom(pat)

      case TuplePattern(binder, subs) =>
        TuplePattern(binder map transform, subs map transform).copiedFrom(pat)

      case UnapplyPattern(binder, id, tps, subs) =>
        UnapplyPattern(binder map transform, id, tps map transform, subs map transform).copiedFrom(pat)

      case PatternExtractor(subs, builder) =>
        builder(subs map transform).copiedFrom(pat)

      case p => p
    }

    def transform(tpe: Type): Type = tpe match {
      case NAryType(ts, builder) => builder(ts map transform).copiedFrom(tpe)
    }
  }

  trait TreeTraverser {
    def traverse(e: Expr): Unit = e match {
      case Variable(_, tpe) =>
        traverse(tpe)

      case Lambda(args, body) =>
        args foreach (vd => traverse(vd.tpe))
        traverse(body)

      case Forall(args, body) =>
        args foreach (vd => traverse(vd.tpe))
        traverse(body)

      case Let(a, expr, body) =>
        traverse(expr)
        traverse(body)

      case CaseClass(cct, args) =>
        traverse(cct)
        args foreach traverse

      case CaseClassSelector(cct, caseClass, selector) =>
        traverse(cct)
        traverse(caseClass)

      case FunctionInvocation(id, tps, args) =>
        tps foreach traverse
        args foreach traverse

      case IsInstanceOf(expr, ct) =>
        traverse(expr)
        traverse(ct)

      case AsInstanceOf(expr, ct) => 
        traverse(expr)
        traverse(ct)

      case MatchExpr(scrutinee, cases) =>
        traverse(scrutinee)
        for (cse @ MatchCase(pattern, guard, rhs) <- cases) {
          traverse(pattern)
          guard foreach traverse
          traverse(rhs)
        }

      case FiniteSet(es, tpe) =>
        es foreach traverse
        traverse(tpe)

      case FiniteBag(es, tpe) =>
        es foreach { case (k, _) => traverse(k) }
        traverse(tpe)

      case FiniteMap(pairs, from, to) =>
        pairs foreach { case (k, v) => traverse(k); traverse(v) }
        traverse(from)
        traverse(to)

      case NoTree(tpe) =>
        traverse(tpe)

      case Error(tpe, desc) =>
        traverse(tpe)

      case Operator(es, builder) =>
        es foreach traverse

      case e =>
    }

    def traverse(pat: Pattern): Unit = pat match {
      case InstanceOfPattern(binder, ct) =>
        traverse(ct)

      case CaseClassPattern(binder, ct, subs) =>
        traverse(ct)
        subs foreach traverse

      case TuplePattern(binder, subs) =>
        subs foreach traverse

      case UnapplyPattern(binder, id, tps, subs) =>
        tps foreach traverse
        subs foreach traverse

      case PatternExtractor(subs, builder) =>
        subs foreach traverse

      case pat =>
    }

    def traverse(tpe: Type): Unit = tpe match {
      case NAryType(ts, builder) =>
        ts foreach traverse
    }
  }
}
