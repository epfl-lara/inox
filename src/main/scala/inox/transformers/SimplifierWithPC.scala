/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

import utils._

import scala.collection.mutable.{Map => MutableMap}

trait SimplifierWithPC extends Transformer { self =>
  val trees: ast.Trees
  val symbols: trees.Symbols

  lazy val s: trees.type = trees
  lazy val t: trees.type = trees

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
    // NOTE: we also rely on the fact that the SolvingPath instance doesn't refer
    //       to the outer simplifier here, otherwise the cast would lead to wrong
    //       simplifications!
    def in(that: SimplifierWithPC {
      val trees: self.trees.type
      val symbols: self.symbols.type
    }): that.Env = this.asInstanceOf[that.Env]
  }

  type Env <: PathLike[Env] with SolvingPath

  def initEnv: Env

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
      val adt @ ADTType(_, tps) = e.getType
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
    case e if path implies e => (BooleanLiteral(true).copiedFrom(e), true)
    case e if path implies not(e) => (BooleanLiteral(false).copiedFrom(e), true)

    case c @ Choose(res, BooleanLiteral(true)) if hasInstance(res.tpe) == Some(true) => (c, true)
    case c: Choose => (c, opts.assumeChecked)

    case Lambda(params, body) =>
      val (rb, _) = simplify(body, path withBounds params)
      (Lambda(params, rb).copiedFrom(e), true)

    case Implies(l, r) => simplify(Or(Not(l).copiedFrom(l), r).copiedFrom(e), path)

    case a @ And(e +: es) => simplify(e, path) match {
      case (BooleanLiteral(true), true) => simplify(andJoin(es).copiedFrom(a), path)
      case (BooleanLiteral(false), true) => (BooleanLiteral(false).copiedFrom(a), true)
      case (re, pe) =>
        val (res, pes) = simplify(andJoin(es).copiedFrom(a), path withCond re)
        if (res == BooleanLiteral(false) && pe) {
          (BooleanLiteral(false).copiedFrom(a), true)
        } else {
          (and(re, res), pe && pes)
        }
    }

    case o @ Or(e +: es) => simplify(e, path) match {
      case (BooleanLiteral(true), true) => (BooleanLiteral(true).copiedFrom(o), true)
      case (BooleanLiteral(false), true) => simplify(orJoin(es).copiedFrom(o), path)
      case (re, pe) =>
        val (res, pes) = simplify(orJoin(es).copiedFrom(o), path withCond Not(re).copiedFrom(re))
        if (res == BooleanLiteral(true) && pe) {
          (BooleanLiteral(true).copiedFrom(o), true)
        } else {
          (or(re, res), pe && pes)
        }
    }

    case ie @ IfExpr(c, t, e) => simplify(c, path) match {
      case (BooleanLiteral(true), true) => simplify(t, path)
      case (BooleanLiteral(false), true) => simplify(e, path)
      case (rc, pc) =>
        val (rt, pt) = simplify(t, path withCond rc)
        val (re, pe) = simplify(e, path withCond Not(rc).copiedFrom(rc))
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
        (Assume(BooleanLiteral(false).copiedFrom(pred), rb).copiedFrom(e), false)
      case (rp, _) =>
        val (rb, _) = simplify(body, path withCond rp)
        (Assume(rp, rb).copiedFrom(e), false)
    }

    case ic @ IsConstructor(e, id) =>
      val (re, pe) = simplify(path expand e, path)
      isConstructor(re, id, path) match {
        case Some(b) if pe => (BooleanLiteral(b).copiedFrom(ic), true)
        case Some(b) => (Let("e" :: re.getType, re, BooleanLiteral(b).copiedFrom(ic)).copiedFrom(ic), pe)
        case None => (IsConstructor(re, id).copiedFrom(ic), pe)
      }

    case s @ ADTSelector(e, sel) =>
      val (re, pe) = simplify(path expand e, path)

      if (isConstructor(re, s.constructor.id, path) == Some(true)) {
        val cons = s.constructor
        val index = cons.definition.selectorID2Index(sel)
        re match {
          case ADT(_, _, es) if pe =>
            (es(index), true)

          // Note: no need to check invariant as if the ADT constructor is in
          //       the path, then its invariant has already been checked.
          case adt @ ADT(_, _, es) =>
            val value = es(index)
            val freshFields = cons.fields.map(_.freshen)
            val bindings = (freshFields zip es).filter(_._2 != value)
            simplify(bindings.foldRight(value) { case ((vd, e), b) => Let(vd, e, b).copiedFrom(s) }, path)

          case _ =>
            (ADTSelector(re, sel).copiedFrom(s), pe)
        }
      } else {
        (ADTSelector(re, sel).copiedFrom(s), opts.assumeChecked)
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
        case _ => ADT(id, tps, rargs).copiedFrom(adt)
      }

      // Note that if `isConstructor(e, id, path)` holds for each ADTSelector argument
      // in rargs, then these selectors will be marked as pure by the simplifier so we
      // don't need to do any special recomputation of pargs
      (newAdt, pargs.foldLeft(opts.assumeChecked || !isImpureExpr(newAdt))(_ && _))

    case ts @ TupleSelect(e, i) => simplify(path expand e, path) match {
      case (Tuple(es), true) => (es(i - 1), true)
      case (Tuple(es), pe) =>
        (es.zipWithIndex.filter(_._2 != i - 1).foldRight(es(i - 1)) {
          case ((e, _), b) => Let("e" :: e.getType, e, b).copiedFrom(ts)
        }, pe)
      case (re, pe) => (TupleSelect(re, i).copiedFrom(ts), pe)
    }

    case Let(vd, IfExpr(c1, t1, e1), IfExpr(c2, t2, e2)) if c1 == c2 =>
      simplify(IfExpr(c1, Let(vd, t1, t2).copiedFrom(e), Let(vd, e1, e2).copiedFrom(e)).copiedFrom(e), path)

    case Let(vd, v: Variable, b) => simplify(replaceFromSymbols(Map(vd -> v), b), path)

    case let @ Let(vd, adt @ ADT(id, tps, es), b) if es.exists { case _: ADT => true case _ => false } =>
      val (nes, bindings) = (adt.getConstructor.fields.map(_.freshen) zip es).map {
        case (vd, a: ADT) => (vd.toVariable, Some(vd -> a))
        case (_, e) => (e, None)
      }.unzip

      simplify(bindings.flatten.foldRight(Let(vd, ADT(id, tps, nes).copiedFrom(adt), b).copiedFrom(let)) {
        case ((vd, e), b) => Let(vd, e, b).copiedFrom(let)
      }, path)

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
        val newLet = Let(vd, re, rb).copiedFrom(let)
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
      (FunctionInvocation(id, tps, rargs).copiedFrom(fi), pargs.foldLeft(isPureFunction(id))(_ && _))

    case n @ Not(e)   => simplifyAndCons(Seq(e), path, es => not(es.head).copiedFrom(n))
    case Equals(l, r) => simplifyAndCons(Seq(l, r), path, es => equality(es(0), es(1)).copiedFrom(e))
    case Tuple(es)    => simplifyAndCons(es, path, es => tupleWrap(es).copiedFrom(e))
    case UMinus(t)    => simplifyAndCons(Seq(t), path, es => uminus(es.head).copiedFrom(e))
    case Plus(l, r)   => simplifyAndCons(Seq(l, r), path, es => plus(es(0), es(1)).copiedFrom(e))
    case Minus(l, r)  => simplifyAndCons(Seq(l, r), path, es => minus(es(0), es(1)).copiedFrom(e))
    case Times(l, r)  => simplifyAndCons(Seq(l, r), path, es => times(es(0), es(1)).copiedFrom(e))

    case Forall(params, body) =>
      simplifyAndCons(Seq(body), path withBounds params, es => simpForall(params, es.head).copiedFrom(e))

    case app @ Application(e, es)  =>
      val (caller, recons): (Expr, Expr => Expr) = simplify(e, path) match {
        case (ra @ Assume(pred, e), _) => (e, assume(pred, _).copiedFrom(ra))
        case (e, _) => (e, expr => expr)
      }

      path.expand(caller) match {
        case (l: Lambda) => simplify(recons(application(l, es)), path)
        case _ =>
          val (res, _) = es.map(simplify(_, path)).unzip
          (application(caller, res).copiedFrom(app), opts.assumeChecked)
      }

    case _ =>
      dynStack.set(0 :: dynStack.get)
      val re = super.transform(e, path)
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

  override final def transform(e: Expr, path: Env): Expr = {
    dynStack.set(if (dynStack.get.isEmpty) Nil else (dynStack.get.head + 1) :: dynStack.get.tail)
    val (re, pe) = simplify(e, path)
    dynPurity.set(if (dynStack.get.isEmpty) dynPurity.get else pe :: dynPurity.get)
    re
  }

  // We make sure to not simplify refinements as this could lead to
  // variable and definition miss-matches during simplification
  override def transform(tpe: Type, path: Env): Type = tpe
}
