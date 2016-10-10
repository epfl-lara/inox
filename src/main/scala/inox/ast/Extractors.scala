/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

/** Meat and bones of tree deconstruction/reconstruction.
  *
  * Implementations provide methods to extract all useful subtrees from
  * a given tree ([[Expressions.Expr]], [[Types.Type]], ...) as well as
  * a closure that can reconstruct the initial tree based on appropriate
  * arguments.
  *
  * Instances of [[Trees]] must provide a [[TreeDeconstructor]] as a
  * means of applying generic transformations to arbitrary extensions of
  * the [[Trees.Tree]] interface.
  *
  * @see [[Extractors]] for some interesting use cases
  */
trait TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  // Basically only provided for ValDefs, but could be extended to other
  // definitions if the users wish to
  def deconstruct(d: s.Definition): (Identifier, Seq[s.Expr], Seq[s.Type], (Identifier, Seq[t.Expr], Seq[t.Type]) => t.Definition) = d match {
    case s.ValDef(id, tpe) => (id, Seq.empty, Seq(tpe), (id, es, tps) => t.ValDef(id, tps.head))
  }

  def deconstruct(expr: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = expr match {
    /* Unary operators */
    case s.Not(e) =>
      (Seq(), Seq(e), Seq(), (_, es, _) => t.Not(es.head))
    case s.BVNot(e) =>
      (Seq(), Seq(e), Seq(), (_, es, _) => t.BVNot(es.head))
    case s.UMinus(e) =>
      (Seq(), Seq(e), Seq(), (_, es, _) => t.UMinus(es.head))
    case s.StringLength(e) =>
      (Seq(), Seq(e), Seq(), (_, es, _) => t.StringLength(es.head))
    case s.ADTSelector(e, sel) =>
      (Seq(), Seq(e), Seq(), (_, es, _) => t.ADTSelector(es.head, sel))
    case s.IsInstanceOf(e, ct) =>
      (Seq(), Seq(e), Seq(ct), (_, es, tps) => t.IsInstanceOf(es.head, tps.head.asInstanceOf[t.ADTType]))
    case s.AsInstanceOf(e, ct) =>
      (Seq(), Seq(e), Seq(ct), (_, es, tps) => t.AsInstanceOf(es.head, tps.head.asInstanceOf[t.ADTType]))
    case s.TupleSelect(e, i) =>
      (Seq(), Seq(e), Seq(), (_, es, _) => t.TupleSelect(es.head, i))
    case s.Lambda(args, body) => (
      args.map(_.toVariable), Seq(body), Seq(),
      (vs, es, _) => t.Lambda(vs.map(_.toVal), es.head))
    case s.Forall(args, body) => (
      args.map(_.toVariable), Seq(body), Seq(),
      (vs, es, _) => t.Forall(vs.map(_.toVal), es.head))
    case s.Choose(res, pred) =>
      (Seq(res.toVariable), Seq(pred), Seq(), (vs, es, _) => t.Choose(vs.head.toVal, es.head))

    /* Binary operators */
    case s.Equals(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Equals(es(0), es(1)))
    case s.Implies(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Implies(es(0), es(1)))
    case s.Plus(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Plus(es(0), es(1)))
    case s.Minus(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Minus(es(0), es(1)))
    case s.Times(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Times(es(0), es(1)))
    case s.Division(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Division(es(0), es(1)))
    case s.Remainder(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Remainder(es(0), es(1)))
    case s.Modulo(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Modulo(es(0), es(1)))
    case s.LessThan(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.LessThan(es(0), es(1)))
    case s.GreaterThan(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.GreaterThan(es(0), es(1)))
    case s.LessEquals(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.LessEquals(es(0), es(1)))
    case s.GreaterEquals(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.GreaterEquals(es(0), es(1)))
    case s.BVOr(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVOr(es(0), es(1)))
    case s.BVAnd(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVAnd(es(0), es(1)))
    case s.BVXor(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVXor(es(0), es(1)))
    case s.BVShiftLeft(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVShiftLeft(es(0), es(1)))
    case s.BVAShiftRight(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVAShiftRight(es(0), es(1)))
    case s.BVLShiftRight(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVLShiftRight(es(0), es(1)))
    case s.StringConcat(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.StringConcat(es(0), es(1)))
    case s.SetAdd(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SetAdd(es(0), es(1)))
    case s.ElementOfSet(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.ElementOfSet(es(0), es(1)))
    case s.SubsetOf(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SubsetOf(es(0), es(1)))
    case s.SetIntersection(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SetIntersection(es(0), es(1)))
    case s.SetUnion(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SetUnion(es(0), es(1)))
    case s.SetDifference(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SetDifference(es(0), es(1)))
    case s.BagAdd(e1, e2) =>
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.BagAdd(es(0), es(1)))
    case s.MultiplicityInBag(e1, e2) =>
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.MultiplicityInBag(es(0), es(1)))
    case s.BagIntersection(e1, e2) =>
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.BagIntersection(es(0), es(1)))
    case s.BagUnion(e1, e2) =>
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.BagUnion(es(0), es(1)))
    case s.BagDifference(e1, e2) =>
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.BagDifference(es(0), es(1)))
    case s.MapUpdated(map, k, v) =>
      (Seq(), Seq(map, k, v), Seq(), (_, es, _) => t.MapUpdated(es(0), es(1), es(2)))
    case s.MapApply(t1, t2) =>
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.MapApply(es(0), es(1)))
    case s.Let(binder, e, body) =>
      (Seq(binder.toVariable), Seq(e, body), Seq(), (vs, es, _) => t.Let(vs.head.toVal, es(0), es(1)))
    case s.Assume(pred, body) =>
      (Seq(), Seq(pred, body), Seq(), (_, es, _) => t.Assume(es(0), es(1)))

    /* Other operators */
    case s.FunctionInvocation(id, tps, args) =>
      (Seq(), args, tps, (_, es, tps) => t.FunctionInvocation(id, tps, es))
    case s.Application(caller, args) =>
      (Seq(), caller +: args, Seq(), (_, es, _) => t.Application(es.head, es.tail))
    case s.ADT(adt, args) =>
      (Seq(), args, Seq(adt), (_, es, tps) => t.ADT(tps.head.asInstanceOf[t.ADTType], es))
    case s.And(args) =>
      (Seq(), args, Seq(), (_, es, _) => t.And(es))
    case s.Or(args) =>
      (Seq(), args, Seq(), (_, es, _) => t.Or(es))
    case s.SubString(t1, a, b) =>
      (Seq(), t1 :: a :: b :: Nil, Seq(), (_, es, _) => t.SubString(es(0), es(1), es(2)))
    case s.FiniteSet(els, base) =>
      (Seq(), els, Seq(base), (_, els, tps) => t.FiniteSet(els, tps.head))
    case s.FiniteBag(els, base) =>
      val subArgs = els.flatMap { case (k, v) => Seq(k, v) }
      val builder = (vs: Seq[t.Variable], as: Seq[t.Expr], tps: Seq[t.Type]) => {
        def rec(kvs: Seq[t.Expr]): Seq[(t.Expr, t.Expr)] = kvs match {
          case Seq(k, v, t @ _*) =>
            Seq(k -> v) ++ rec(t)
          case Seq() => Seq()
          case _ => sys.error("odd number of key/value expressions")
        }
        t.FiniteBag(rec(as), tps.head)
      }
      (Seq(), subArgs, Seq(base), builder)
    case s.FiniteMap(elems, default, kT) =>
      val subArgs = elems.flatMap { case (k, v) => Seq(k, v) } :+ default
      val builder = (vs: Seq[t.Variable], as: Seq[t.Expr], kT: Seq[t.Type]) => {
        def rec(kvs: Seq[t.Expr]): (Seq[(t.Expr, t.Expr)], t.Expr) = kvs match {
          case Seq(k, v, t @ _*) =>
            val (kvs, default) = rec(t)
            (Seq(k -> v) ++ kvs, default)
          case Seq(default) => (Seq(), default)
        }
        val (pairs, default) = rec(as)
        t.FiniteMap(pairs, default, kT.head)
      }
      (Seq(), subArgs, Seq(kT), builder)
    case s.Tuple(args) =>
      (Seq(), args, Seq(), (_, es, _) => t.Tuple(es))
    case s.IfExpr(cond, thenn, elze) => (
      Seq(), Seq(cond, thenn, elze), Seq(),
      (_, es, _) => t.IfExpr(es(0), es(1), es(2)))

    case v @ s.Variable(id, tp) =>
      (Seq(v), Seq(), Seq(), (vs, _, _) => vs.head)

    case s.GenericValue(tp, id) =>
      (Seq(), Seq(), Seq(tp), (_, _, tps) => t.GenericValue(tps.head.asInstanceOf[t.TypeParameter], id))
    case s.CharLiteral(ch) =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.CharLiteral(ch))
    case s.BVLiteral(bits, size) =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.BVLiteral(bits, size))
    case s.IntegerLiteral(i) =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.IntegerLiteral(i))
    case s.FractionLiteral(n, d) =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.FractionLiteral(n, d))
    case s.BooleanLiteral(b) =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.BooleanLiteral(b))
    case s.StringLiteral(st) =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.StringLiteral(st))
    case s.UnitLiteral() =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.UnitLiteral())
  }

  def deconstruct(tp: s.Type): (Seq[s.Type], Seq[t.Type] => t.Type) = tp match {
    case s.ADTType(d, ts) => (ts, ts => t.ADTType(d, ts))
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

  def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.HasADTInvariant(id) =>
      (Seq(), Seq(), (_, _) => t.HasADTInvariant(id))
    case s.Annotation(name, args) =>
      val withIndex = args.zipWithIndex
      val (exprs, exprIndexes) = withIndex.collect { case (e: s.Expr, i) => e -> i }.unzip
      val (types, typeIndexes) = withIndex.collect { case (tp: s.Type, i) => tp -> i }.unzip

      // we use the implicit contract on Flags here that states that a flag is either
      // an instance of Expr | Type, or it has nothing to do with a tree
      val rest = withIndex.filterNot(_._1.isInstanceOf[s.Tree])
      (exprs, types, (es, tps) => t.Annotation(name,
        ((es zip exprIndexes) ++ (tps zip typeIndexes) ++ rest).sortBy(_._2).map(_._1)
      ))
  }
}

/** Provides extraction capabilities to [[Trees]] based on a
  * [[TreeDeconstructor]] instance. */
trait Extractors { self: Trees =>

  val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  }

  /** Operator Extractor to extract any Expression in a consistent way.
    *
    * You can match on any Inox Expr, and then get both a Seq[Expr] of
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
      val (vs, es, tps, builder) = deconstructor.deconstruct(e)
      Some(es, ess => builder(vs, ess, tps))
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
