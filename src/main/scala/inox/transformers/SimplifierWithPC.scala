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

  class CNFPath private(
    private val exprSubst: Bijection[Variable, Expr],
    private val boolSubst: Map[Variable, Expr],
    private val conditions: Set[Expr],
    private val cnfCache: MutableMap[Expr, Seq[Expr]],
    private val simpCache: MutableMap[Expr, Set[Expr]]) extends PathLike[CNFPath] {

    import exprOps._

    def subsumes(that: CNFPath): Boolean =
      (conditions subsetOf that.conditions) &&
      (exprSubst.forall { case (k, e) => that.exprSubst.getB(k).exists(_ == e) }) &&
      (boolSubst.forall { case (k, e) => that.boolSubst.get(k).exists(_ == e) })

    private def unexpandLets(e: Expr, exprSubst: Bijection[Variable, Expr] = exprSubst): Expr = {
      postMap(exprSubst.getA)(e)
    }

    def contains(e: Expr) = {
      val TopLevelOrs(es) = unexpandLets(e)
      conditions contains orJoin(es.distinct.sortBy(_.hashCode))
    }

    def expand(e: Expr): Expr = e match {
      case v: Variable => (exprSubst getB v) orElse (boolSubst get v) match {
        case Some(v2: Variable) => expand(v2)
        case Some(e2 @ (_: ADT | _: Tuple)) => e2
        case _ => e
      }
      case _ => e
    }

    private def cnf(e: Expr): Seq[Expr] = cnfCache.getOrElseUpdate(e, e match {
      case Let(i, e, b) => cnf(b).map(Let(i, e, _))
      case And(es) => es.flatMap(cnf)
      case Or(es) => es.map(cnf).foldLeft(Seq(BooleanLiteral(false): Expr)) {
        case (clauses, es) => es.flatMap(e => clauses.map(c => or(e, c)))
      }
      case IfExpr(c, t, e) => cnf(and(implies(c, t), implies(not(c), e)))
      case Implies(l, r) => cnf(or(not(l), r))
      case Not(Or(es)) => cnf(andJoin(es.map(not)))
      case Not(Implies(l, r)) => cnf(and(l, not(r)))
      case Not(Not(e)) => cnf(e)
      case IsConstructor(e, id) =>
        Seq(IsConstructor(e, id)) ++
        getConstructor(id).getSort.constructors.filterNot(_.id == id).map(c => Not(IsConstructor(e, c.id)))
      case e => Seq(e)
    })

    private def simplify(e: Expr): Expr = self.simplify(e, this)._1

    private def simplifyClauses(e: Expr): Expr = andJoin(getClauses(e).toSeq.sortBy(_.hashCode))

    private def getClauses(e: Expr): Set[Expr] = simpCache.getOrElseUpdate(e, {
      val (preds, newE) = liftAssumptions(simplifyLets(unexpandLets(e)))
      val expr = andJoin(newE +: preds)
      simpCache.getOrElseUpdate(expr, {
        val clauseSet: MutableSet[Expr] = MutableSet.empty
        for (cl <- cnf(expr); TopLevelOrs(es) <- cnf(replaceFromSymbols(boolSubst, simplify(cl)))) {
          clauseSet += orJoin(es.distinct.sortBy(_.hashCode))
        }

        var changed = true
        while (changed) {
          changed = false
          for (cls @ TopLevelOrs(es) <- clauseSet) {
            val eSet = es.toSet
            if (
              cls == BooleanLiteral(true) ||
              es.exists(e => conditions(e) || (eSet contains not(e))) ||
              (es.size > 1 && es.exists(e => clauseSet(e)))
            ) {
              clauseSet -= cls
            } else {
              val newCls = orJoin(es.filter(e => !clauseSet(not(e)) && !conditions(not(e))))
              if (newCls != cls) {
                clauseSet -= cls
                clauseSet += newCls
                changed = true
              }
            }
          }
        }

        clauseSet.toSet
      })
    })

    override def withBinding(p: (ValDef, Expr)) = {
      val (vd, expr) = p

      val extraConds: Set[Expr] = expr match {
        case ADT(id, _, _) => cnf(IsConstructor(vd.toVariable, id)).toSet
        case _ => Set()
      }

      if (formulaSize(expr) > 20) {
        new CNFPath(exprSubst, boolSubst, conditions ++ extraConds, cnfCache, simpCache)
      } else if (vd.tpe == BooleanType()) {
        new CNFPath(exprSubst, boolSubst + (vd.toVariable -> simplifyClauses(expr)), conditions, cnfCache, simpCache)
      } else {
        val newSubst = exprSubst.clone += (vd.toVariable -> unexpandLets(expr))
        val newBools = boolSubst.mapValues(e => simplifyClauses(unexpandLets(e, newSubst)))
        val newConds = conditions.map(unexpandLets(_, newSubst))

        /* @nv: it seems the performance gain through extra cache hits is completely overshadowed by
         *      the cost of traversing the caches to update them, so this optimization is now disabled.
        cnfCache ++= cnfCache.map { case (k, v) => unexpandLets(k, newSubst) -> v.map(unexpandLets(_, newSubst)) }
        simpCache ++= simpCache.map { case (k, v) => unexpandLets(k, newSubst) -> v.map(unexpandLets(_, newSubst)) }
        */

        new CNFPath(newSubst, newBools, newConds ++ extraConds, cnfCache, simpCache)
      }
    }

    override def withBound(b: ValDef) = this // NOTE CNFPath doesn't need to track such bounds.

    override def withCond(e: Expr) = if (formulaSize(e) > 20) this else {
      val clauses = getClauses(e)
      val newConditions = conditions.flatMap { case clause @ TopLevelOrs(es) =>
        val newClause = orJoin(es.filterNot(e => clauses contains not(e)))
        if (newClause != clause) cnf(newClause) else Seq(clause)
      }

      val conds = newConditions ++ clauses - BooleanLiteral(true)
      new CNFPath(exprSubst, boolSubst, conds, cnfCache, simpCache)
    }

    override def merge(that: CNFPath) = new CNFPath(
      exprSubst.clone ++= that.exprSubst,
      boolSubst ++ that.boolSubst,
      conditions ++ that.conditions,
      cnfCache ++= that.cnfCache,
      simpCache ++= that.simpCache
    )

    override def negate = new CNFPath(exprSubst, boolSubst, Set(), cnfCache, simpCache) withConds conditions.map(not)

    def asString(implicit opts: PrinterOptions): String = andJoin(conditions.toSeq.sortBy(_.hashCode)).asString

    override def toString = asString(PrinterOptions.fromContext(Context.printNames))
  }

  implicit object CNFPath extends PathProvider[CNFPath] {
    def empty = new CNFPath(new Bijection[Variable, Expr], Map.empty, Set.empty, MutableMap.empty, MutableMap.empty)
    def apply(path: Path) = path.elements.foldLeft(empty) {
      case (path, Path.CloseBound(vd, e)) => path withBinding (vd -> transform(e, path))
      case (path, Path.OpenBound(_)) => path // NOTE CNFPath doesn't need to track such bounds.
      case (path, Path.Condition(c)) => path withCond transform(c, path)
    }
  }

  type Env = CNFPath

  // @nv: note that we make sure the initial env is fresh each time
  //      (since aggressive caching of cnf computations is taking place)
  def initEnv: CNFPath = CNFPath.empty

  private[this] val dynStack: DynamicVariable[List[Int]] = new DynamicVariable(Nil)
  private[this] val dynPurity: DynamicVariable[List[Boolean]] = new DynamicVariable(Nil)

  private sealed abstract class PurityCheck
  private case object Pure extends PurityCheck
  private case object Impure extends PurityCheck
  private case object Checking extends PurityCheck

  private[this] val pureCache: MutableMap[Identifier, PurityCheck] = MutableMap.empty

  protected final def isPureFunction(id: Identifier): Boolean = {
    opts.assumeChecked ||
    synchronized(pureCache.get(id) match {
      case Some(Pure) => true
      case Some(Impure) => false
      case Some(Checking) =>
        // Function is recursive and cycles were not pruned by the simplifier.
        // No need to update pureCache here as the update will take place in the next branch.
        false
      case None =>
        pureCache += id -> Checking
        val p = isPure(getFunction(id).fullBody, CNFPath.empty)
        pureCache += id -> (if (p) Pure else Impure)
        p
    })
  }

  protected def isConstructor(e: Expr, id: Identifier, path: CNFPath): Option[Boolean] = e match {
    case ADT(id2, _, _) => Some(id == id2)
    case _ => if (path contains IsConstructor(e, id)) {
      Some(true)
    } else if (path contains Not(IsConstructor(e, id))) {
      Some(false)
    } else {
      val adt @ ADTType(_, tps) = widen(e.getType)
      val sort = adt.getSort
      val cons = getConstructor(id, tps)
      val alts = (sort.constructors.toSet - cons).map(_.id)

      if (alts exists (id => path contains IsConstructor(e, id))) {
        Some(false)
      } else if (alts forall (id => path contains Not(IsConstructor(e, id)))) {
        Some(true)
      } else {
        None
      }
    }
  }

  final def isPure(e: Expr, path: CNFPath): Boolean = simplify(e, path)._2

  private class SimplificationCache(cache: Cache[Expr, (CNFPath, Expr, Boolean)]) {
    def cached(e: Expr, path: CNFPath)(body: => (Expr, Boolean)): (Expr, Boolean) =
      cache.get(e)
        .filter { case (p, _, _) => (p subsumes path) }
        .map { case (_, re, pe) => (re, pe) }
        .getOrElse {
          val (re, pe) = body
          cache(e) = (path, re, pe)
          (re, pe)
        }
  }

  private val recentCache = new SimplificationCache(new LruCache(100))

  protected def simplify(e: Expr, path: CNFPath): (Expr, Boolean) = e match {
    case e if path contains e => (BooleanLiteral(true), true)
    case e if path contains not(e) => (BooleanLiteral(false), true)

    case c @ Choose(res, BooleanLiteral(true)) if hasInstance(res.tpe) == Some(true) => (c, true)
    case c: Choose => (c, opts.assumeChecked)

    case Lambda(args, body) =>
      val (rb, _) = simplify(body, path)
      (Lambda(args, rb), true)

    case Implies(l, r) => simplify(or(not(l), r), path)

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
        val (res, pes) = simplify(orJoin(es), path withCond not(re))
        if (res == BooleanLiteral(true) && pe) {
          (BooleanLiteral(true), true)
        } else {
          (or(re, res), pe && pes)
        }
    }

    case IfExpr(c, t, e) => simplify(c, path) match {
      case (BooleanLiteral(true), true) => simplify(t, path)
      case (BooleanLiteral(false), true) => simplify(e, path)
      case (rc, pc) =>
        val (rt, pt) = simplify(t, path withCond rc)
        val (re, pe) = simplify(e, path withCond not(rc))
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
        (Assume(BooleanLiteral(false), rb), opts.assumeChecked)
      case (rp, _) =>
        val (rb, _) = simplify(body, path withCond rp)
        (Assume(rp, rb), opts.assumeChecked)
    }

    case IsConstructor(e, id) =>
      val (re, pe) = simplify(path.expand(e), path)
      isConstructor(re, id, path) match {
        case Some(b) if pe => (BooleanLiteral(b), true)
        case Some(b) => (Let("e" :: re.getType, re, BooleanLiteral(b)), pe)
        case None => (IsConstructor(re, id), pe)
      }

    case s @ ADTSelector(e, sel) =>
      val (re, pe) = simplify(path.expand(e), path)

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

    case TupleSelect(e, i) => simplify(path.expand(e), path) match {
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
    case let @ Let(vd, e, b) => recentCache.cached(let, path) {
      val (re, pe) = simplify(e, path)
      val (rb, pb) = simplify(b, path withBinding (vd -> re))

      val v = vd.toVariable
      lazy val insts = count { case `v` => 1 case _ => 0 }(rb)
      lazy val inLambda = exists { case l: Lambda => variablesOf(l) contains v case _ => false }(rb)
      lazy val immediateCall = existsWithPC(rb) { case (`v`, path) => path.isEmpty case _ => false }
      lazy val containsLambda = exists { case l: Lambda => true case _ => false }(re)
      lazy val realPE = if (opts.assumeChecked) {
        val simp = simplifier(solvers.PurityOptions.unchecked)
        simp.isPure(e, path.asInstanceOf[simp.CNFPath])
      } else {
        pe
      }

      if (
        (((!inLambda && pe) || (inLambda && realPE && !containsLambda)) && insts <= 1) ||
        (!inLambda && immediateCall && insts == 1)
      ) {
        val newExpr = replaceFromSymbols(Map(vd -> re), rb)
        re match {
          // If the bound expression was an ADT or variable, then `path.expand` has already
          // made sure that all possible simplifications have taken place in `rb`.
          case (_: ADT | _: Variable) => (newExpr, pe && pb)
          case _ => simplify(newExpr, path)
        }
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

    case Application(e, es)  => simplify(e, path) match {
      case (l: Lambda, _) => simplify(application(l, es), path)
      case (Assume(pred, l: Lambda), _) => simplify(assume(pred, application(l, es)), path)
      case (re, _) =>
        val (res, _) = es.map(simplify(_, path)).unzip
        (application(re, res), opts.assumeChecked)
    }

    case _ =>
      dynStack.value = 0 :: dynStack.value
      val re = super.rec(e, path)
      val (rpure, rest) = dynPurity.value.splitAt(dynStack.value.head)
      val pe = rpure.foldLeft(opts.assumeChecked || !isImpureExpr(re))(_ && _)
      dynStack.value = dynStack.value.tail
      dynPurity.value = rest
      (re, pe)
  }

  private def simplifyAndCons(es: Seq[Expr], path: CNFPath, cons: Seq[Expr] => Expr): (Expr, Boolean) = {
    val (res, pes) = es.map(simplify(_, path)).unzip
    val re = cons(res)
    val pe = pes.foldLeft(opts.assumeChecked || !isImpureExpr(re))(_ && _)
    (re, pe)
  }

  override protected final def rec(e: Expr, path: CNFPath): Expr = {
    dynStack.value = if (dynStack.value.isEmpty) Nil else (dynStack.value.head + 1) :: dynStack.value.tail
    val (re, pe) = simplify(e, path)
    dynPurity.value = if (dynStack.value.isEmpty) dynPurity.value else pe :: dynPurity.value
    re
  }
}

