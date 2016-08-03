/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait Extractors { self: Trees =>

  /** Operator Extractor to extract any Expression in a consistent way.
    *
    * You can match on any Leon Expr, and then get both a Seq[Expr] of
    * subterms and a builder fonction that takes a Seq of subterms (of same
    * length) and rebuild the original node.
    *
    * Those extractors do not perform any syntactic simplifications. They
    * rebuild the node using the case class (not the constructor, that performs
    * simplifications). The rational behind this decision is to have core
    * tools for performing tree transformations that are very predictable, if
    * one need to simplify the tree, it is easy to write/call a simplification
    * function that would simply apply the corresponding constructor for each node.
    */
  object Operator extends TreeExtractor {
    val trees: Extractors.this.type = Extractors.this
    type SubTree = trees.Expr

    def unapply(expr: Expr): Option[(Seq[Expr], (Seq[Expr]) => Expr)] = expr match {
      /* Unary operators */
      case Not(t) =>
        Some((Seq(t), (es: Seq[Expr]) => Not(es.head)))
      case UMinus(t) =>
        Some((Seq(t), (es: Seq[Expr]) => UMinus(es.head)))
      case StringLength(t) =>
        Some((Seq(t), (es: Seq[Expr]) => StringLength(es.head)))
      case SetCardinality(t) =>
        Some((Seq(t), (es: Seq[Expr]) => SetCardinality(es.head)))
      case CaseClassSelector(e, sel) =>
        Some((Seq(e), (es: Seq[Expr]) => CaseClassSelector(es.head, sel)))
      case IsInstanceOf(e, ct) =>
        Some((Seq(e), (es: Seq[Expr]) => IsInstanceOf(es.head, ct)))
      case AsInstanceOf(e, ct) =>
        Some((Seq(e), (es: Seq[Expr]) => AsInstanceOf(es.head, ct)))
      case TupleSelect(t, i) =>
        Some((Seq(t), (es: Seq[Expr]) => TupleSelect(es.head, i)))
      case Lambda(args, body) =>
        Some((Seq(body), (es: Seq[Expr]) => Lambda(args, es.head)))
      case Forall(args, body) =>
        Some((Seq(body), (es: Seq[Expr]) => Forall(args, es.head)))

      /* Binary operators */
      case Equals(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Equals(es(0), es(1)))
      case Implies(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Implies(es(0), es(1)))
      case Plus(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Plus(es(0), es(1)))
      case Minus(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Minus(es(0), es(1)))
      case Times(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Times(es(0), es(1)))
      case Division(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Division(es(0), es(1)))
      case Remainder(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Remainder(es(0), es(1)))
      case Modulo(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => Modulo(es(0), es(1)))
      case LessThan(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => LessThan(es(0), es(1)))
      case GreaterThan(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => GreaterThan(es(0), es(1)))
      case LessEquals(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => LessEquals(es(0), es(1)))
      case GreaterEquals(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => GreaterEquals(es(0), es(1)))
      case BVXOr(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVXOr(es(0), es(1)))
      case BVShiftLeft(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVShiftLeft(es(0), es(1)))
      case BVAShiftRight(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVAShiftRight(es(0), es(1)))
      case BVLShiftRight(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => BVLShiftRight(es(0), es(1)))
      case StringConcat(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => StringConcat(es(0), es(1)))
      case SetAdd(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SetAdd(es(0), es(1)))
      case ElementOfSet(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => ElementOfSet(es(0), es(1)))
      case SubsetOf(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SubsetOf(es(0), es(1)))
      case SetIntersection(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SetIntersection(es(0), es(1)))
      case SetUnion(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SetUnion(es(0), es(1)))
      case SetDifference(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => SetDifference(es(0), es(1)))
      case BagAdd(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => BagAdd(es(0), es(1)))
      case MultiplicityInBag(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => MultiplicityInBag(es(0), es(1)))
      case BagIntersection(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => BagIntersection(es(0), es(1)))
      case BagUnion(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => BagUnion(es(0), es(1)))
      case BagDifference(e1, e2) =>
        Some(Seq(e1, e2), (es: Seq[Expr]) => BagDifference(es(0), es(1)))
      case mg @ MapApply(t1, t2) =>
        Some(Seq(t1, t2), (es: Seq[Expr]) => MapApply(es(0), es(1)))
      case Let(binder, e, body) =>
        Some(Seq(e, body), (es: Seq[Expr]) => Let(binder, es(0), es(1)))

      /* Other operators */
      case fi @ FunctionInvocation(fd, tps, args) => Some((args, FunctionInvocation(fd, tps, _)))
      case fa @ Application(caller, args) => Some(caller +: args, as => Application(as.head, as.tail))
      case CaseClass(cd, args) => Some((args, CaseClass(cd, _)))
      case And(args) => Some((args, es => And(es)))
      case Or(args) => Some((args, es => Or(es)))
      case SubString(t1, a, b) => Some((t1::a::b::Nil, es => SubString(es(0), es(1), es(2))))
      case FiniteSet(els, base) =>
        Some((els, els => FiniteSet(els, base)))
      case FiniteBag(els, base) =>
        val subArgs = els.flatMap { case (k, v) => Seq(k, v) }.toSeq
        val builder = (as: Seq[Expr]) => {
          def rec(kvs: Seq[Expr]): Seq[(Expr, Expr)] = kvs match {
            case Seq(k, v, t @ _*) =>
              Seq(k -> v) ++ rec(t)
            case Seq() => Seq()
            case _ => sys.error("odd number of key/value expressions")
          }
          FiniteBag(rec(as), base)
        }
        Some((subArgs, builder))
      case FiniteMap(args, f, t) => {
        val subArgs = args.flatMap { case (k, v) => Seq(k, v) }.toSeq
        val builder = (as: Seq[Expr]) => {
          def rec(kvs: Seq[Expr]): Seq[(Expr, Expr)] = kvs match {
            case Seq(k, v, t @ _*) =>
              Seq(k -> v) ++ rec(t)
            case Seq() => Seq()
            case _ => sys.error("odd number of key/value expressions")
          }
          FiniteMap(rec(as), f, t)
        }
        Some((subArgs, builder))
      }
      case Tuple(args) => Some((args, es => Tuple(es)))
      case IfExpr(cond, thenn, elze) => Some((
        Seq(cond, thenn, elze),
        { case Seq(c, t, e) => IfExpr(c, t, e) }
      ))

      /* Terminals */
      case t: Terminal => Some(Seq[Expr](), (_:Seq[Expr]) => t)

      /* Expr's not handled here should implement this trait */
      case e: Extractable =>
        e.extract

      case _ =>
        None
    }
  }

  // Extractors for types are available at Types.NAryType

  trait Extractable {
    def extract: Option[(Seq[Expr], Seq[Expr] => Expr)]
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
