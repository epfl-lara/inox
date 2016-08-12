/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast


trait TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  def deconstruct(expr: s.Expr): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Expr) = expr match {
    /* Unary operators */
    case s.Not(e) =>
      (Seq(e), Seq(), (es, tps) => t.Not(es.head))
    case s.BVNot(e) =>
      (Seq(e), Seq(), (es, tps) => t.BVNot(es.head))
    case s.UMinus(e) =>
      (Seq(e), Seq(), (es, tps) => t.UMinus(es.head))
    case s.StringLength(e) =>
      (Seq(e), Seq(), (es, tps) => t.StringLength(es.head))
    case s.SetCardinality(e) =>
      (Seq(e), Seq(), (es, tps) => t.SetCardinality(es.head))
    case s.CaseClassSelector(e, sel) =>
      (Seq(e), Seq(), (es, tps) => t.CaseClassSelector(es.head, sel))
    case s.IsInstanceOf(e, ct) =>
      (Seq(e), Seq(ct), (es, tps) => t.IsInstanceOf(es.head, tps.head.asInstanceOf[t.ClassType]))
    case s.AsInstanceOf(e, ct) =>
      (Seq(e), Seq(ct), (es, tps) => t.AsInstanceOf(es.head, tps.head.asInstanceOf[t.ClassType]))
    case s.TupleSelect(e, i) =>
      (Seq(e), Seq(), (es, tps) => t.TupleSelect(es.head, i))
    case s.Lambda(args, body) => (
      Seq(body), args.map(_.tpe),
      (es, tps) => t.Lambda(args.zip(tps).map(p => t.ValDef(p._1.id, p._2)), es.head))
    case s.Forall(args, body) => (
      Seq(body), args.map(_.tpe),
      (es, tps) => t.Forall(args.zip(tps).map(p => t.ValDef(p._1.id, p._2)), es.head))
    case s.Choose(res, pred) =>
      (Seq(pred), Seq(res.tpe), (es, tps) => t.Choose(t.ValDef(res.id, tps.head), es.head))

    /* Binary operators */
    case s.Equals(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.Equals(es(0), es(1)))
    case s.Implies(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.Implies(es(0), es(1)))
    case s.Plus(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.Plus(es(0), es(1)))
    case s.Minus(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.Minus(es(0), es(1)))
    case s.Times(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.Times(es(0), es(1)))
    case s.Division(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.Division(es(0), es(1)))
    case s.Remainder(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.Remainder(es(0), es(1)))
    case s.Modulo(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.Modulo(es(0), es(1)))
    case s.LessThan(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.LessThan(es(0), es(1)))
    case s.GreaterThan(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.GreaterThan(es(0), es(1)))
    case s.LessEquals(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.LessEquals(es(0), es(1)))
    case s.GreaterEquals(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.GreaterEquals(es(0), es(1)))
    case s.BVOr(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.BVOr(es(0), es(1)))
    case s.BVAnd(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.BVAnd(es(0), es(1)))
    case s.BVXOr(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.BVXOr(es(0), es(1)))
    case s.BVShiftLeft(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.BVShiftLeft(es(0), es(1)))
    case s.BVAShiftRight(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.BVAShiftRight(es(0), es(1)))
    case s.BVLShiftRight(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.BVLShiftRight(es(0), es(1)))
    case s.StringConcat(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.StringConcat(es(0), es(1)))
    case s.SetAdd(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.SetAdd(es(0), es(1)))
    case s.ElementOfSet(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.ElementOfSet(es(0), es(1)))
    case s.SubsetOf(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.SubsetOf(es(0), es(1)))
    case s.SetIntersection(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.SetIntersection(es(0), es(1)))
    case s.SetUnion(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.SetUnion(es(0), es(1)))
    case s.SetDifference(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.SetDifference(es(0), es(1)))
    case s.BagAdd(e1, e2) =>
      (Seq(e1, e2), Seq(), (es, tps) => t.BagAdd(es(0), es(1)))
    case s.MultiplicityInBag(e1, e2) =>
      (Seq(e1, e2), Seq(), (es, tps) => t.MultiplicityInBag(es(0), es(1)))
    case s.BagIntersection(e1, e2) =>
      (Seq(e1, e2), Seq(), (es, tps) => t.BagIntersection(es(0), es(1)))
    case s.BagUnion(e1, e2) =>
      (Seq(e1, e2), Seq(), (es, tps) => t.BagUnion(es(0), es(1)))
    case s.BagDifference(e1, e2) =>
      (Seq(e1, e2), Seq(), (es, tps) => t.BagDifference(es(0), es(1)))
    case s.MapUpdated(map, k, v) =>
      (Seq(map, k, v), Seq(), (es, tps) => t.MapUpdated(es(0), es(1), es(2)))
    case s.MapApply(t1, t2) =>
      (Seq(t1, t2), Seq(), (es, tps) => t.MapApply(es(0), es(1)))
    case s.Let(binder, e, body) =>
      (Seq(e, body), Seq(binder.tpe), (es, tps) => t.Let(t.ValDef(binder.id, tps.head), es(0), es(1)))

    /* Other operators */
    case s.FunctionInvocation(id, tps, args) =>
      (args, tps, (es, tps) => t.FunctionInvocation(id, tps, es))
    case s.Application(caller, args) => (caller +: args, Seq(), (es, tps) => t.Application(es.head, es.tail))
    case s.CaseClass(ct, args) => (args, Seq(ct), (es, tps) => t.CaseClass(tps.head.asInstanceOf[t.ClassType], es))
    case s.And(args) => (args, Seq(), (es, _) => t.And(es))
    case s.Or(args) => (args, Seq(), (es, _) => t.Or(es))
    case s.SubString(t1, a, b) => (t1 :: a :: b :: Nil, Seq(), (es, _) => t.SubString(es(0), es(1), es(2)))
    case s.FiniteSet(els, base) =>
      (els, Seq(base), (els, tps) => t.FiniteSet(els, tps.head))
    case s.FiniteBag(els, base) =>
      val subArgs = els.flatMap { case (k, v) => Seq(k, v) }
      val builder = (as: Seq[t.Expr], tps: Seq[t.Type]) => {
        def rec(kvs: Seq[t.Expr]): Seq[(t.Expr, t.Expr)] = kvs match {
          case Seq(k, v, t @ _*) =>
            Seq(k -> v) ++ rec(t)
          case Seq() => Seq()
          case _ => sys.error("odd number of key/value expressions")
        }
        t.FiniteBag(rec(as), tps.head)
      }
      (subArgs, Seq(base), builder)
    case s.FiniteMap(elems, default, kT) =>
      val subArgs = elems.flatMap { case (k, v) => Seq(k, v) } :+ default
      val builder = (as: Seq[t.Expr], kT: Seq[t.Type]) => {
        def rec(kvs: Seq[t.Expr]): (Seq[(t.Expr, t.Expr)], t.Expr) = kvs match {
          case Seq(k, v, t @ _*) =>
            val (kvs, default) = rec(t)
            (Seq(k -> v) ++ kvs, default)
          case Seq(default) => (Seq(), default)
        }
        val (pairs, default) = rec(as)
        t.FiniteMap(pairs, default, kT.head)
      }
      (subArgs, Seq(kT), builder)
    case s.Tuple(args) => (args, Seq(), (es, _) => t.Tuple(es))
    case s.IfExpr(cond, thenn, elze) => (
      Seq(cond, thenn, elze), Seq(),
      (es, _) => t.IfExpr(es(0), es(1), es(2)))

    case s.Variable(id, tp) =>
      (Seq(), Seq(tp), (_, tps) => t.Variable(id, tps.head))

    case s.GenericValue(tp, id) =>
      (Seq(), Seq(tp), (_, tps) => t.GenericValue(tps.head.asInstanceOf[t.TypeParameter], id))

    case s.CharLiteral(ch) =>
      (Seq(), Seq(), (_, _) => t.CharLiteral(ch))

    case s.BVLiteral(bits, size) =>
      (Seq(), Seq(), (_, _) => t.BVLiteral(bits, size))

    case s.IntegerLiteral(i) =>
      (Seq(), Seq(), (_, _) => t.IntegerLiteral(i))

    case s.FractionLiteral(n, d) =>
      (Seq(), Seq(), (_, _) => t.FractionLiteral(n, d))

    case s.BooleanLiteral(b) =>
      (Seq(), Seq(), (_, _) => t.BooleanLiteral(b))

    case s.StringLiteral(st) =>
      (Seq(), Seq(), (_, _) => t.StringLiteral(st))

    case s.UnitLiteral() =>
      (Seq(), Seq(), (_, _) => t.UnitLiteral())
  }

  def deconstruct(tp: s.Type): (Seq[s.Type], Seq[t.Type] => t.Type) = tp match {
    case s.ClassType(ccd, ts) => (ts, ts => t.ClassType(ccd, ts))
    case s.TupleType(ts) => (ts, t.TupleType)
    case s.SetType(tp) => (Seq(tp), ts => t.SetType(ts.head))
    case s.BagType(tp) => (Seq(tp), ts => t.BagType(ts.head))
    case s.MapType(from,to) => (Seq(from, to), ts => t.MapType(ts(0), ts(1)))
    case s.FunctionType(fts, tt) => (tt +: fts, ts => t.FunctionType(ts.tail.toList, ts.head))

    case s.TypeParameter(id) => (Seq(), _ => t.TypeParameter(id))
    case s.BVType(size) => (Seq(), _ => t.BVType(size))

    case s.Untyped     => (Seq(), _ => t.Untyped)
    case s.BooleanType => (Seq(), _ => t.BooleanType)
    case s.UnitType    => (Seq(), _ => t.UnitType)
    case s.CharType    => (Seq(), _ => t.CharType)
    case s.IntegerType => (Seq(), _ => t.IntegerType)
    case s.RealType    => (Seq(), _ => t.RealType)
    case s.StringType  => (Seq(), _ => t.StringType)
  }

  def translate(e: s.Expr): t.Expr = {
    val (es, tps, builder) = deconstruct(e)

    var changed = false
    val newEs = for (e <- es) yield {
      val newE = translate(e)
      if (e ne newE) changed = true
      newE
    }

    val newTps = for (tp <- tps) yield {
      val newTp = translate(tp)
      if (tp ne newTp) changed = true
      newTp
    }

    if (changed || (s ne t)) {
      builder(newEs, newTps).copiedFrom(e)
    } else {
      e.asInstanceOf[t.Expr]
    }
  }

  def translate(tp: s.Type): t.Type = {
    val (tps, builder) = deconstruct(tp)

    var changed = false
    val newTps = for (tp <- tps) yield {
      val newTp = translate(tp)
      if (tp ne newTp) changed = true
      newTp
    }

    if (changed || (s ne t)) {
      builder(newTps).copiedFrom(tp)
    } else {
      tp.asInstanceOf[t.Type]
    }
  }
}

trait Extractors { self: Trees =>

  val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  }

  /** Operator Extractor to extract any Expression in a consistent way.
    *
    * You can match on any Leon Expr, and then get both a Seq[Expr] of
    * subterms and a builder function that takes a Seq of subterms (of same
    * length) and rebuild the original node.
    *
    * Those extractors do not perform any syntactic simplifications. They
    * rebuild the node using the case class (not the constructor, that performs
    * simplifications). The rational behind this decision is to have core
    * tools for performing tree transformations that are very predictable, if
    * one need to simplify the tree, it is easy to write/call a simplification
    * function that would simply apply the corresponding constructor for each node.
    */
  object Operator extends {
    protected val s: self.type = self
    protected val t: self.type = self
  } with TreeExtractor {
    type Source = Expr
    type Target = Expr

    def unapply(e: Expr): Option[(Seq[Expr], Seq[Expr] => Expr)] = {
      val (es, tps, builder) = deconstructor.deconstruct(e)
      Some(es, ess => builder(ess, tps))
    }
  }

  object TopLevelOrs { // expr1 OR (expr2 OR (expr3 OR ..)) => List(expr1, expr2, expr3)
    def unapply(e: Expr): Option[Seq[Expr]] = e match {
      case Let(i, e, TopLevelOrs(bs)) => Some(bs map (Let(i,e,_)))
      case Or(exprs) =>
        Some(exprs.flatMap(unapply).flatten)
      case e =>
        Some(Seq(e))
    }
  }

  object TopLevelAnds { // expr1 AND (expr2 AND (expr3 AND ..)) => List(expr1, expr2, expr3)
    def unapply(e: Expr): Option[Seq[Expr]] = e match {
      case Let(i, e, TopLevelAnds(bs)) => Some(bs map (Let(i,e,_)))
      case And(exprs) =>
        Some(exprs.flatMap(unapply).flatten)
      case e =>
        Some(Seq(e))
    }
  }

  object IsTyped {
    def unapply[T <: Typed](e: T)(implicit p: Symbols): Option[(T, Type)] = Some((e, e.getType))
  }

  def unwrapTuple(e: Expr, isTuple: Boolean)(implicit s: Symbols): Seq[Expr] = e.getType match {
    case TupleType(subs) if isTuple => 
      for (ind <- 1 to subs.size) yield { s.tupleSelect(e, ind, isTuple) }
    case _ if !isTuple => Seq(e)
    case tp => sys.error(s"Calling unwrapTuple on non-tuple $e of type $tp")
  }

  def unwrapTuple(e: Expr, expectedSize: Int)(implicit p: Symbols): Seq[Expr] = unwrapTuple(e, expectedSize > 1)

  def unwrapTupleType(tp: Type, isTuple: Boolean): Seq[Type] = tp match {
    case TupleType(subs) if isTuple => subs
    case tp if !isTuple => Seq(tp)
    case tp => sys.error(s"Calling unwrapTupleType on $tp")
  }

  def unwrapTupleType(tp: Type, expectedSize: Int): Seq[Type] =
    unwrapTupleType(tp, expectedSize > 1)
}
