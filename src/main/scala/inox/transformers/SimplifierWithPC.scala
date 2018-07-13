/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

import utils._

import scala.util.DynamicVariable
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait SimplifierWithPC extends TransformerWithPC { self =>
  import trees._
  import symbols._
  import exprOps._
  import dsl._

  implicit val opts: solvers.PurityOptions

  trait SolvingPath { selfP: Env =>
    def expand(expr: Expr): Expr = expr
    def implies(expr: Expr): Boolean

    // @nv: Scala's type system is unfortunately not powerful enough to express
    //      what we want here. The type should actually specify that the `that`
    //      parameter is the same type as this simplifier.
    def in(that: SimplifierWithPC {
      val trees: self.trees.type
      val symbols: self.symbols.type
    }): that.Env = this.asInstanceOf[that.Env]
  }

  type Env <: PathLike[Env] with SolvingPath

  private[this] val dynStack = new ThreadLocal[List[Int]] { override def initialValue = Nil }
  private[this] val dynPurity = new ThreadLocal[List[Boolean]] { override def initialValue = Nil }

  private sealed abstract class PurityCheck
  private case object Pure extends PurityCheck
  private case object Impure extends PurityCheck
  private case object Checking extends PurityCheck

  private[this] val pureCache: MutableMap[Identifier, PurityCheck] = MutableMap.empty

  protected final def isPureFunction(id: Identifier): Boolean = synchronized(pureCache.get(id) match {
    case Some(Pure) => true
    case Some(Impure) => false
    case Some(Checking) =>
      // Function is recursive and cycles were not pruned by the simplifier.
      // No need to update pureCache here as the update will take place in the next branch.
      opts.assumeChecked
    case None =>
      pureCache += id -> Checking
      val p = isPure(getFunction(id).fullBody, initEnv)
      pureCache += id -> (if (p) Pure else Impure)
      p
  })

  protected def isConstructor(e: Expr, id: Identifier, path: Env): Option[Boolean] = e match {
    case ADT(id2, _, _) => Some(id == id2)
    case _ => if (path implies IsConstructor(e, id)) {
      Some(true)
    } else if (path implies Not(IsConstructor(e, id))) {
      Some(false)
    } else {
      val adt @ ADTType(_, tps) = widen(e.getType)
      val sort = adt.getSort
      val cons = getConstructor(id, tps)
      val alts = (sort.constructors.toSet - cons).map(_.id)

      if (alts exists (id => path implies IsConstructor(e, id))) {
        Some(false)
      } else if (alts forall (id => path implies Not(IsConstructor(e, id)))) {
        Some(true)
      } else {
        None
      }
    }
  }

  final def isPure(e: Expr, path: Env): Boolean = simplify(e, path)._2

  protected def simplify(e: Expr, path: Env): (Expr, Boolean) = e match {
    case e if path implies e => (BooleanLiteral(true), true)
    case e if path implies not(e) => (BooleanLiteral(false), true)

    case c @ Choose(res, BooleanLiteral(true)) if hasInstance(res.tpe) == Some(true) => (c, true)
    case c: Choose => (c, opts.assumeChecked)

    case Lambda(args, body) =>
      val (rb, _) = simplify(body, path)
      (Lambda(args, rb), true)

    case Implies(l, r) => simplify(Or(Not(l), r), path)

    case And(e +: es) => simplify(e, path) match {
      case (BooleanLiteral(true), true) => simplify(andJoin(es), path)
      case (BooleanLiteral(false), true) => (BooleanLiteral(false), true)
      case (re, pe) =>
        val (res, pes) = simplify(andJoin(es), path withCond re)
        if (res == BooleanLiteral(false) && pe) {
          (BooleanLiteral(false), true)
        } else {
          (and(re, res), pe && pes)
        }
    }

    case Or(e +: es) => simplify(e, path) match {
      case (BooleanLiteral(true), true) => (BooleanLiteral(true), true)
      case (BooleanLiteral(false), true) => simplify(orJoin(es), path)
      case (re, pe) =>
        val (res, pes) = simplify(orJoin(es), path withCond Not(re))
        if (res == BooleanLiteral(true) && pe) {
          (BooleanLiteral(true), true)
        } else {
          (or(re, res), pe && pes)
        }
    }

    case ie @ IfExpr(c, t, e) => simplify(c, path) match {
      case (BooleanLiteral(true), true) => simplify(t, path)
      case (BooleanLiteral(false), true) => simplify(e, path)
      case (rc, pc) =>
        val (rt, pt) = simplify(t, path withCond rc)
        val (re, pe) = simplify(e, path withCond Not(rc))
        if (rt == re && pc) {
          (rt, pt)
        } else {
          (ifExpr(rc, rt, re), pc && pt && pe)
        }
    }

    case Assume(pred, body) => simplify(pred, path) match {
      case (BooleanLiteral(true), true) => simplify(body, path)
      case (BooleanLiteral(false), true) =>
        val (rb, _) = simplify(body, path)
        (Assume(BooleanLiteral(false), rb), false)
      case (rp, _) =>
        val (rb, _) = simplify(body, path withCond rp)
        (Assume(rp, rb), false)
    }

    case IsConstructor(e, id) =>
      val (re, pe) = simplify(path expand e, path)
      isConstructor(re, id, path) match {
        case Some(b) if pe => (BooleanLiteral(b), true)
        case Some(b) => (Let("e" :: re.getType, re, BooleanLiteral(b)), pe)
        case None => (IsConstructor(re, id), pe)
      }

    case s @ ADTSelector(e, sel) =>
      val (re, pe) = simplify(path expand e, path)

      if (isConstructor(re, s.constructor.id, path) == Some(true)) {
        val cons = s.constructor
        val index = cons.definition.selectorID2Index(sel)
        re match {
          case ADT(_, _, es) if pe =>
            (es(index), true)
          case adt @ ADT(_, _, es) /*if !adt.getConstructor.sort.hasInvariant*/ =>
            val value = es(index)
            val freshFields = cons.fields.map(_.freshen)
            val bindings = (freshFields zip es).filter(_._2 != value)
            simplify(bindings.foldRight(value) { case ((vd, e), b) => Let(vd, e, b) }, path)
          case _ =>
            (ADTSelector(re, sel), pe)
        }
      } else {
        (ADTSelector(re, sel), opts.assumeChecked)
      }

    case adt @ ADT(id, tps, args) =>
      val (rargs, pargs) = args.map(simplify(_, path)).unzip
      val ls = (adt.getConstructor.fields zip rargs).collect {
        case (vd, ADTSelector(e, id)) if vd.id == id => e
      }

      val newAdt = ls match {
        case ls @ (e +: es) if (
          ls.size == rargs.size &&
          es.forall(_ == e) &&
          e.getType == adt.getType &&
          (isConstructor(e, id, path) contains true)) => e
        case _ => ADT(id, tps, rargs)
      }
      // Note that if `isConstructor(e, id, path)` holds for each ADTSelector argument
      // in rargs, then these selectors will be marked as pure by the simplifier so we
      // don't need to do any special recomputation of pargs
      val pe = pargs.foldLeft(opts.assumeChecked || !isImpureExpr(newAdt))(_ && _)
      (newAdt, pe)

    case TupleSelect(e, i) => simplify(path expand e, path) match {
      case (Tuple(es), true) => (es(i - 1), true)
      case (Tuple(es), pe) =>
        (es.zipWithIndex.filter(_._2 != i - 1).foldRight(es(i - 1)) {
          case ((e, _), b) => Let("e" :: e.getType, e, b)
        }, pe)
      case (re, pe) => (TupleSelect(re, i), pe)
    }

    case Let(vd, IfExpr(c1, t1, e1), IfExpr(c2, t2, e2)) if c1 == c2 =>
      simplify(IfExpr(c1, Let(vd, t1, t2), Let(vd, e1, e2)), path)

    case Let(vd, v: Variable, b) => simplify(replaceFromSymbols(Map(vd -> v), b), path)

    case Let(vd, adt @ ADT(id, tps, es), b) if es.exists { case _: ADT => true case _ => false } =>
      val (nes, bindings) = (adt.getConstructor.fields.map(_.freshen) zip es).map {
        case (vd, a: ADT) => (vd.toVariable, Some(vd -> a))
        case (_, e) => (e, None)
      }.unzip

      simplify(bindings.flatten.foldRight(Let(vd, ADT(id, tps, nes), b)) {
        case ((vd, e), b) => Let(vd, e, b)
      }, path)

    // @nv: Simplifying lets can lead to exponential simplification cost.
    //      The `recentCache` greatly reduces the cost of simplifying lets but
    //      there are still corner cases that will make this expensive.
    //      In `assumeChecked` mode, the cost should be lower as most lets with
    //      `insts <= 1` will be inlined immediately.
    case let @ Let(vd, e, b) =>
      val (re, pe) = simplify(e, path)
      val (rb, pb) = simplify(b, path withBinding (vd -> re))

      val v = vd.toVariable
      lazy val insts = count { case `v` => 1 case _ => 0 }(rb)
      lazy val inLambda = exists { case l: Lambda => variablesOf(l) contains v case _ => false }(rb)
      lazy val immediateCall = existsWithPC(rb) { case (`v`, path) => path.isEmpty case _ => false }
      lazy val containsLambda = exists { case l: Lambda => true case _ => false }(re)
      lazy val realPE = if (opts.assumeChecked) {
        val simp = simplifier(solvers.PurityOptions.unchecked)
        simp.isPure(e, path in simp)
      } else {
        pe
      }

      if (
        (((!inLambda && pe) || (inLambda && realPE && !containsLambda)) && insts <= 1) ||
        (!inLambda && immediateCall && insts == 1)
      ) {
        // We can assume here that all `important` simplifications have already taken place
        // as if the bound expression was an ADT or variable, then `path.expand` has already
        // made sure that all possible simplifications have taken place in `rb`.
        (replaceFromSymbols(Map(vd -> re), rb), pe && pb)
      } else {
        val newLet = Let(vd, re, rb)
        re match {
          case l: Lambda =>
            val inlined = inlineLambdas(newLet)
            if (inlined != newLet) simplify(inlined, path)
            else (newLet, pe && pb)
          case _ => (newLet, pe && pb)
        }
      }

    case fi @ FunctionInvocation(id, tps, args) =>
      val (rargs, pargs) = args.map(simplify(_, path)).unzip
      (FunctionInvocation(id, tps, rargs), pargs.foldLeft(isPureFunction(id))(_ && _))

    case Not(e)              => simplifyAndCons(Seq(e), path, es => not(es.head))
    case Equals(l, r)        => simplifyAndCons(Seq(l, r), path, es => equality(es(0), es(1)))
    case Tuple(es)           => simplifyAndCons(es, path, tupleWrap)
    case UMinus(t)           => simplifyAndCons(Seq(t), path, es => uminus(es.head))
    case Plus(l, r)          => simplifyAndCons(Seq(l, r), path, es => plus(es(0), es(1)))
    case Minus(l, r)         => simplifyAndCons(Seq(l, r), path, es => minus(es(0), es(1)))
    case Times(l, r)         => simplifyAndCons(Seq(l, r), path, es => times(es(0), es(1)))
    case Forall(args, body)  => simplifyAndCons(Seq(body), path, es => simpForall(args, es.head))

    case Application(e, es)  =>
      val (caller, recons): (Expr, Expr => Expr) = simplify(e, path) match {
        case (Assume(pred, e), _) => (e, assume(pred, _))
        case (e, _) => (e, expr => expr)
      }

      path.expand(caller) match {
        case (l: Lambda) => simplify(recons(application(l, es)), path)
        case _ =>
          val (res, _) = es.map(simplify(_, path)).unzip
          (application(caller, res), opts.assumeChecked)
      }

    case _ =>
      dynStack.set(0 :: dynStack.get)
      val re = super.rec(e, path)
      val (rpure, rest) = dynPurity.get.splitAt(dynStack.get.head)
      val pe = rpure.foldLeft(opts.assumeChecked || !isImpureExpr(re))(_ && _)
      dynStack.set(dynStack.get.tail)
      dynPurity.set(rest)
      (re, pe)
  }

  private def simplifyAndCons(es: Seq[Expr], path: Env, cons: Seq[Expr] => Expr): (Expr, Boolean) = {
    val (res, pes) = es.map(simplify(_, path)).unzip
    val re = cons(res)
    val pe = pes.foldLeft(opts.assumeChecked || !isImpureExpr(re))(_ && _)
    (re, pe)
  }

  override protected final def rec(e: Expr, path: Env): Expr = {
    dynStack.set(if (dynStack.get.isEmpty) Nil else (dynStack.get.head + 1) :: dynStack.get.tail)
    val (re, pe) = simplify(e, path)
    dynPurity.set(if (dynStack.get.isEmpty) dynPurity.get else pe :: dynPurity.get)
    re
  }
}

trait FastSimplifier extends SimplifierWithPC {
  import trees._
  import symbols._
  import exprOps._
  import dsl._

  class Env private(
    private val conditions: Set[Expr],
    private val exprSubst: Map[Variable, Expr]
  ) extends PathLike[Env] with SolvingPath {

    override def withBinding(p: (ValDef, Expr)): Env = p match {
      case (vd, expr @ (_: ADT | _: Tuple | _: Lambda)) =>
        new Env(conditions, exprSubst + (vd.toVariable -> expr))
      case (vd, v: Variable) =>
        val exp = expand(v)
        if (v != exp) new Env(conditions, exprSubst + (vd.toVariable -> exp))
        else this
      case _ => this
    }

    override def withBound(vd: ValDef): Env = this // We don't need to track such bounds.

    override def withCond(cond: Expr): Env = new Env(conditions + cond, exprSubst)

    override def negate: Env =
      new Env(Set(), exprSubst) withConds conditions.toSeq.map(not)

    override def merge(that: Env): Env =
      new Env(conditions ++ that.conditions, exprSubst ++ that.exprSubst)

    override def expand(expr: Expr): Expr = expr match {
      case v: Variable => exprSubst.getOrElse(v, v)
      case _ => expr
    }

    override def implies(expr: Expr): Boolean = conditions contains expr

    override def toString: String = conditions.toString
  }

  implicit object Env extends PathProvider[Env] {
    def empty = new Env(Set(), Map())
  }

  override def initEnv = Env.empty
}
