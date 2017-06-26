/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

import scala.collection.immutable.HashMap

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

  /** Rebuild an expression from the given set of variables, subexpressions and types */
  type ExprBuilder = (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr

  /** Extracted subtrees from an expression as well as a "builder" */
  type DeconstructedExpr = (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], ExprBuilder)

  /** Optimisation trick for large pattern matching sequence: jumps directly to the correct case based
    * on the type of the expression -- a kind of virtual table for pattern matching.
    *
    * NOTE using the following shorthand make things significantly slower,
    * even slower than ordering the regular pattern matching cases according
    * to their frequencies.
    *
    *     classOf[s.Not] -> { case s.Not(e) => /* ... */ }
    */
  private val exprTable: Map[Class[_], s.Expr => DeconstructedExpr] = HashMap(
    /* Unary operators */
    classOf[s.Not] -> { expr =>
      val s.Not(e) = expr
      (Seq(), Seq(e), Seq(), (_, es, _) => t.Not(es.head))
    },
    classOf[s.BVNot] -> { expr =>
      val s.BVNot(e) = expr
      (Seq(), Seq(e), Seq(), (_, es, _) => t.BVNot(es.head))
    },
    classOf[s.UMinus] -> { expr =>
      val s.UMinus(e) = expr
      (Seq(), Seq(e), Seq(), (_, es, _) => t.UMinus(es.head))
    },
    classOf[s.StringLength] -> { expr =>
      val s.StringLength(e) = expr
      (Seq(), Seq(e), Seq(), (_, es, _) => t.StringLength(es.head))
    },
    classOf[s.ADTSelector] -> { expr =>
      val s.ADTSelector(e, sel) = expr
      (Seq(), Seq(e), Seq(), (_, es, _) => t.ADTSelector(es.head, sel))
    },
    classOf[s.IsInstanceOf] -> { expr =>
      val s.IsInstanceOf(e, ct) = expr
      (Seq(), Seq(e), Seq(ct), (_, es, tps) => t.IsInstanceOf(es.head, tps.head))
    },
    classOf[s.AsInstanceOf] -> { expr =>
      val s.AsInstanceOf(e, ct) = expr
      (Seq(), Seq(e), Seq(ct), (_, es, tps) => t.AsInstanceOf(es.head, tps.head))
    },
    classOf[s.TupleSelect] -> { expr =>
      val s.TupleSelect(e, i) = expr
      (Seq(), Seq(e), Seq(), (_, es, _) => t.TupleSelect(es.head, i))
    },
    classOf[s.Lambda] -> { expr =>
      val s.Lambda(args, body) = expr
      (args.map(_.toVariable), Seq(body), Seq(),
      (vs, es, _) => t.Lambda(vs.map(_.toVal), es.head))
    },
    classOf[s.Forall] -> { expr =>
      val s.Forall(args, body) = expr
      (args.map(_.toVariable), Seq(body), Seq(),
      (vs, es, _) => t.Forall(vs.map(_.toVal), es.head))
    },
    classOf[s.Choose] -> { expr =>
      val s.Choose(res, pred) = expr
      (Seq(res.toVariable), Seq(pred), Seq(), (vs, es, _) => t.Choose(vs.head.toVal, es.head))
    },

    /* Binary operators */
    classOf[s.Equals] -> { expr =>
      val s.Equals(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Equals(es(0), es(1)))
    },
    classOf[s.Implies] -> { expr =>
      val s.Implies(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Implies(es(0), es(1)))
    },
    classOf[s.Plus] -> { expr =>
      val s.Plus(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Plus(es(0), es(1)))
    },
    classOf[s.Minus] -> { expr =>
      val s.Minus(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Minus(es(0), es(1)))
    },
    classOf[s.Times] -> { expr =>
      val s.Times(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Times(es(0), es(1)))
    },
    classOf[s.Division] -> { expr =>
      val s.Division(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Division(es(0), es(1)))
    },
    classOf[s.Remainder] -> { expr =>
      val s.Remainder(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Remainder(es(0), es(1)))
    },
    classOf[s.Modulo] -> { expr =>
      val s.Modulo(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.Modulo(es(0), es(1)))
    },
    classOf[s.LessThan] -> { expr =>
      val s.LessThan(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.LessThan(es(0), es(1)))
    },
    classOf[s.GreaterThan] -> { expr =>
      val s.GreaterThan(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.GreaterThan(es(0), es(1)))
    },
    classOf[s.LessEquals] -> { expr =>
      val s.LessEquals(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.LessEquals(es(0), es(1)))
    },
    classOf[s.GreaterEquals] -> { expr =>
      val s.GreaterEquals(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.GreaterEquals(es(0), es(1)))
    },
    classOf[s.BVOr] -> { expr =>
      val s.BVOr(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVOr(es(0), es(1)))
    },
    classOf[s.BVAnd] -> { expr =>
      val s.BVAnd(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVAnd(es(0), es(1)))
    },
    classOf[s.BVXor] -> { expr =>
      val s.BVXor(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVXor(es(0), es(1)))
    },
    classOf[s.BVShiftLeft] -> { expr =>
      val s.BVShiftLeft(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVShiftLeft(es(0), es(1)))
    },
    classOf[s.BVAShiftRight] -> { expr =>
      val s.BVAShiftRight(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVAShiftRight(es(0), es(1)))
    },
    classOf[s.BVLShiftRight] -> { expr =>
      val s.BVLShiftRight(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.BVLShiftRight(es(0), es(1)))
    },
    classOf[s.BVNarrowingCast] -> { expr =>
      val s.BVNarrowingCast(e, bvt) = expr
      (Seq(), Seq(e), Seq(bvt), (_, es, tps) => t.BVNarrowingCast(es(0), tps(0).asInstanceOf[t.BVType]))
    },
    classOf[s.BVWideningCast] -> { expr =>
      val s.BVWideningCast(e, bvt) = expr
      (Seq(), Seq(e), Seq(bvt), (_, es, tps) => t.BVWideningCast(es(0), tps(0).asInstanceOf[t.BVType]))
    },
    classOf[s.StringConcat] -> { expr =>
      val s.StringConcat(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.StringConcat(es(0), es(1)))
    },
    classOf[s.SetAdd] -> { expr =>
      val s.SetAdd(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SetAdd(es(0), es(1)))
    },
    classOf[s.ElementOfSet] -> { expr =>
      val s.ElementOfSet(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.ElementOfSet(es(0), es(1)))
    },
    classOf[s.SubsetOf] -> { expr =>
      val s.SubsetOf(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SubsetOf(es(0), es(1)))
    },
    classOf[s.SetIntersection] -> { expr =>
      val s.SetIntersection(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SetIntersection(es(0), es(1)))
    },
    classOf[s.SetUnion] -> { expr =>
      val s.SetUnion(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SetUnion(es(0), es(1)))
    },
    classOf[s.SetDifference] -> { expr =>
      val s.SetDifference(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.SetDifference(es(0), es(1)))
    },
    classOf[s.BagAdd] -> { expr =>
      val s.BagAdd(e1, e2) = expr
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.BagAdd(es(0), es(1)))
    },
    classOf[s.MultiplicityInBag] -> { expr =>
      val s.MultiplicityInBag(e1, e2) = expr
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.MultiplicityInBag(es(0), es(1)))
    },
    classOf[s.BagIntersection] -> { expr =>
      val s.BagIntersection(e1, e2) = expr
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.BagIntersection(es(0), es(1)))
    },
    classOf[s.BagUnion] -> { expr =>
      val s.BagUnion(e1, e2) = expr
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.BagUnion(es(0), es(1)))
    },
    classOf[s.BagDifference] -> { expr =>
      val s.BagDifference(e1, e2) = expr
      (Seq(), Seq(e1, e2), Seq(), (_, es, _) => t.BagDifference(es(0), es(1)))
    },
    classOf[s.MapUpdated] -> { expr =>
      val s.MapUpdated(map, k, v) = expr
      (Seq(), Seq(map, k, v), Seq(), (_, es, _) => t.MapUpdated(es(0), es(1), es(2)))
    },
    classOf[s.MapApply] -> { expr =>
      val s.MapApply(t1, t2) = expr
      (Seq(), Seq(t1, t2), Seq(), (_, es, _) => t.MapApply(es(0), es(1)))
    },
    classOf[s.Let] -> { expr =>
      val s.Let(binder, e, body) = expr
      (Seq(binder.toVariable), Seq(e, body), Seq(), (vs, es, _) => t.Let(vs.head.toVal, es(0), es(1)))
    },
    classOf[s.Assume] -> { expr =>
      val s.Assume(pred, body) = expr
      (Seq(), Seq(pred, body), Seq(), (_, es, _) => t.Assume(es(0), es(1)))
    },

    /* Other operators */
    classOf[s.FunctionInvocation] -> { expr =>
      val s.FunctionInvocation(id, tps, args) = expr
      (Seq(), args, tps, (_, es, tps) => t.FunctionInvocation(id, tps, es))
    },
    classOf[s.Application] -> { expr =>
      val s.Application(caller, args) = expr
      (Seq(), caller +: args, Seq(), (_, es, _) => t.Application(es.head, es.tail))
    },
    classOf[s.ADT] -> { expr =>
      val s.ADT(adt, args) = expr
      (Seq(), args, Seq(adt), (_, es, tps) => t.ADT(tps.head.asInstanceOf[t.ADTType], es))
    },
    classOf[s.And] -> { expr =>
      val s.And(args) = expr
      (Seq(), args, Seq(), (_, es, _) => t.And(es))
    },
    classOf[s.Or] -> { expr =>
      val s.Or(args) = expr
      (Seq(), args, Seq(), (_, es, _) => t.Or(es))
    },
    classOf[s.SubString] -> { expr =>
      val s.SubString(t1, a, b) = expr
      (Seq(), t1 :: a :: b :: Nil, Seq(), (_, es, _) => t.SubString(es(0), es(1), es(2)))
    },
    classOf[s.FiniteSet] -> { expr =>
      val s.FiniteSet(els, base) = expr
      (Seq(), els, Seq(base), (_, els, tps) => t.FiniteSet(els, tps.head))
    },
    classOf[s.FiniteBag] -> { expr =>
      val s.FiniteBag(els, base) = expr
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
    },
    classOf[s.FiniteMap] -> { expr =>
      val s.FiniteMap(elems, default, kT, vT) = expr
      val subArgs = elems.flatMap { case (k, v) => Seq(k, v) } :+ default
      val builder = (vs: Seq[t.Variable], as: Seq[t.Expr], tps: Seq[t.Type]) => {
        def rec(kvs: Seq[t.Expr]): (Seq[(t.Expr, t.Expr)], t.Expr) = kvs match {
          case Seq(k, v, t @ _*) =>
            val (kvs, default) = rec(t)
            (Seq(k -> v) ++ kvs, default)
          case Seq(default) => (Seq(), default)
        }
        val (pairs, default) = rec(as)
        t.FiniteMap(pairs, default, tps(0), tps(1))
      }
      (Seq(), subArgs, Seq(kT, vT), builder)
    },
    classOf[s.Tuple] -> { expr =>
      val s.Tuple(args) = expr
      (Seq(), args, Seq(), (_, es, _) => t.Tuple(es))
    },
    classOf[s.IfExpr] -> { expr =>
      val s.IfExpr(cond, thenn, elze) = expr
      (Seq(), Seq(cond, thenn, elze), Seq(),
      (_, es, _) => t.IfExpr(es(0), es(1), es(2)))
    },

    classOf[s.Variable] -> { expr =>
      val v = expr.asInstanceOf[s.Variable]
      (Seq(v), Seq(), Seq(), (vs, _, _) => vs.head)
    },

    classOf[s.GenericValue] -> { expr =>
      val s.GenericValue(tp, id) = expr
      (Seq(), Seq(), Seq(tp), (_, _, tps) => t.GenericValue(tps.head.asInstanceOf[t.TypeParameter], id))
    },
    classOf[s.CharLiteral] -> { expr =>
      val s.CharLiteral(ch) = expr
      (Seq(), Seq(), Seq(), (_, _, _) => t.CharLiteral(ch))
    },
    classOf[s.BVLiteral] -> { expr =>
      val s.BVLiteral(bits, size) = expr
      (Seq(), Seq(), Seq(), (_, _, _) => t.BVLiteral(bits, size))
    },
    classOf[s.IntegerLiteral] -> { expr =>
      val s.IntegerLiteral(i) = expr
      (Seq(), Seq(), Seq(), (_, _, _) => t.IntegerLiteral(i))
    },
    classOf[s.FractionLiteral] -> { expr =>
      val s.FractionLiteral(n, d) = expr
      (Seq(), Seq(), Seq(), (_, _, _) => t.FractionLiteral(n, d))
    },
    classOf[s.BooleanLiteral] -> { expr =>
      val s.BooleanLiteral(b) = expr
      (Seq(), Seq(), Seq(), (_, _, _) => t.BooleanLiteral(b))
    },
    classOf[s.StringLiteral] -> { expr =>
      val s.StringLiteral(st) = expr
      (Seq(), Seq(), Seq(), (_, _, _) => t.StringLiteral(st))
    },
    classOf[s.UnitLiteral] -> { expr =>
      val s.UnitLiteral() = expr
      (Seq(), Seq(), Seq(), (_, _, _) => t.UnitLiteral())
    }
  )

  def deconstruct(expr: s.Expr): DeconstructedExpr = exprTable(expr.getClass)(expr)

  def deconstruct(tp: s.Type): (Seq[s.Type], Seq[s.Flag], (Seq[t.Type], Seq[t.Flag]) => t.Type) = tp match {
    case s.ADTType(d, ts) => (ts, Seq(), (ts, _) => t.ADTType(d, ts))
    case s.TupleType(ts) => (ts, Seq(), (ts, _) => t.TupleType(ts))
    case s.SetType(tp) => (Seq(tp), Seq(), (ts, _) => t.SetType(ts.head))
    case s.BagType(tp) => (Seq(tp), Seq(), (ts, _) => t.BagType(ts.head))
    case s.MapType(from,to) => (Seq(from, to), Seq(), (ts, _) => t.MapType(ts(0), ts(1)))
    case s.FunctionType(fts, tt) => (tt +: fts, Seq(),  (ts, _) => t.FunctionType(ts.tail.toList, ts.head))

    case s.TypeParameter(id, flags) => (Seq(), flags.toSeq, (_, flags) => t.TypeParameter(id, flags.toSet))
    case s.BVType(size) => (Seq(), Seq(), (_, _) => t.BVType(size))

    case s.Untyped     => (Seq(), Seq(), (_, _) => t.Untyped)
    case s.BooleanType => (Seq(), Seq(), (_, _) => t.BooleanType)
    case s.UnitType    => (Seq(), Seq(), (_, _) => t.UnitType)
    case s.CharType    => (Seq(), Seq(), (_, _) => t.CharType)
    case s.IntegerType => (Seq(), Seq(), (_, _) => t.IntegerType)
    case s.RealType    => (Seq(), Seq(), (_, _) => t.RealType)
    case s.StringType  => (Seq(), Seq(), (_, _) => t.StringType)
  }

  def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.Variance(v) =>
      (Seq(), Seq(), (_, _) => t.Variance(v))
    case s.HasADTInvariant(id) =>
      (Seq(), Seq(), (_, _) => t.HasADTInvariant(id))
    case s.HasADTEquality(id) =>
      (Seq(), Seq(), (_, _) => t.HasADTEquality(id))
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

  def getDeconstructor(that: Trees): TreeDeconstructor {
    val s: self.type
    val t: that.type
  } = new TreeDeconstructor {
    protected val s: self.type = self
    protected val t: that.type = that
  }

  val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  } = getDeconstructor(self)

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

  object CNF {
    def unapply(e: Expr): Option[Seq[Expr]] = Some(exprOps.toCNF(e))
  }

  object IsTyped {
    def unapply[T <: Typed](e: T)(implicit s: Symbols): Option[(T, Type)] = Some((e, e.getType))
  }

  def unwrapTuple(e: Expr, isTuple: Boolean)(implicit s: Symbols): Seq[Expr] = e.getType match {
    case TupleType(subs) if isTuple =>
      for (ind <- 1 to subs.size) yield { s.tupleSelect(e, ind, isTuple) }
    case _ if !isTuple => Seq(e)
    case tp => sys.error(s"Calling unwrapTuple on non-tuple $e of type $tp")
  }

  def unwrapTuple(e: Expr, expectedSize: Int)(implicit s: Symbols): Seq[Expr] = unwrapTuple(e, expectedSize > 1)

  def unwrapTupleType(tp: Type, isTuple: Boolean): Seq[Type] = tp match {
    case TupleType(subs) if isTuple => subs
    case tp if !isTuple => Seq(tp)
    case tp => sys.error(s"Calling unwrapTupleType on $tp")
  }

  def unwrapTupleType(tp: Type, expectedSize: Int): Seq[Type] =
    unwrapTupleType(tp, expectedSize > 1)

  object RecordType {
    def unapply(tpe: ADTType)(implicit s: Symbols): Option[TypedADTConstructor] = tpe.getADT match {
      case tcons: TypedADTConstructor if !tcons.definition.isInductive => Some(tcons)
      case tsort: TypedADTSort if tsort.constructors.size == 1 => unapply(tsort.constructors.head.toType)
      case _ => None
    }
  }

  object FunctionContainerType {
    def unapply(tpe: Type)(implicit s: Symbols): Boolean = {
      def rec(tpe: Type, first: Boolean = false): Boolean = tpe match {
        case RecordType(tcons) => tcons.fieldsTypes.exists(rec(_))
        case TupleType(tpes) => tpes.exists(rec(_))
        case _: FunctionType if !first => true
        case _ => false
      }

      rec(tpe, first = true)
    }
  }

  object Container {
    def unapply(e: Expr)(implicit s: Symbols): Option[(Seq[Expr], Seq[Expr] => Expr)] = e.getType match {
      case adt @ RecordType(tcons) =>
        Some((tcons.fields.map(vd => ADTSelector(e, vd.id)), es => ADT(adt, es)))

      case TupleType(tps) =>
        Some((tps.indices.map(i => TupleSelect(e, i + 1)).toSeq, es => Tuple(es)))

      case _ => None
    }
  }
}
