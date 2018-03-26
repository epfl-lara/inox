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

  val opts: solvers.PurityOptions

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
      case e => Seq(e)
    })

    private def simplify(e: Expr): Expr = transform(e, this)

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
      if (formulaSize(expr) > 20) {
        this
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

        new CNFPath(newSubst, newBools, newConds, cnfCache, simpCache)
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

    override def toString = conditions.toString
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

  private[this] var dynStack: DynamicVariable[List[Int]] = new DynamicVariable(Nil)
  private[this] var dynPurity: DynamicVariable[List[Boolean]] = new DynamicVariable(Nil)

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

  protected def isConstructor(e: Expr, id: Identifier, path: CNFPath): Option[Boolean] = {
    if (path contains IsConstructor(e, id)) {
      Some(true)
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

  def isPure(e: Expr, path: CNFPath): Boolean = simplify(e, path)._2

  private val simplifyCache = new LruCache[Expr, (CNFPath, Expr, Boolean)](100)

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

    case IsConstructor(adt @ ADT(id1, tps, args), id2) =>
      simplify((adt.getConstructor.fields zip args)
        .foldRight(BooleanLiteral(id1 == id2): Expr) {
          case ((vd, e), body) => Let(vd.freshen, e, body)
        }, path)

    case IsConstructor(e, id) =>
      val (re, pe) = simplify(e, path)
      isConstructor(re, id, path) match {
        case Some(b) => (BooleanLiteral(b), true)
        case None => (IsConstructor(re, id), pe)
      }

    case s @ ADTSelector(e, sel) =>
      val (re, pe) = simplify(e, path)
      isConstructor(re, s.constructor.id, path) match {
        case Some(true) => (adtSelector(re, sel), pe)
        case _ => (ADTSelector(re, sel), opts.assumeChecked)
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

    case Let(vd, IfExpr(c1, t1, e1), IfExpr(c2, t2, e2)) if c1 == c2 =>
      simplify(IfExpr(c1, Let(vd, t1, t2), Let(vd, e1, e2)), path)

    case Let(vd, v: Variable, b) => simplify(replaceFromSymbols(Map(vd -> v), b), path)

    case Let(vd, adt @ ADT(id, tps, es), b) if (
      (opts.assumeChecked || !adt.getConstructor.sort.hasInvariant) && {
        val v = vd.toVariable
        def rec(e: Expr): Boolean = e match {
          case ADTSelector(`v`, id) => true
          case `v` => false
          case Operator(es, _) => es.forall(rec)
        }
        rec(b)
      }) =>
      val cons = adt.getConstructor
      val vds = cons.fields.map(_.freshen)
      val selectors = cons.fields.map(f => ADTSelector(vd.toVariable, f.id))
      val selectorMap: Map[Expr, Expr] = (selectors zip vds.map(_.toVariable)).toMap
      simplify((vds zip es).foldRight(replace(selectorMap, b)) { case ((vd, e), b) => Let(vd, e, b) }, path)

    // @nv: Simplifying lets can lead to exponential simplification cost.
    //      The `simplifyCache` greatly reduces the cost of simplifying lets but
    //      there are still corner cases that will make this expensive.
    //      In `assumeChecked` mode, the cost should be lower as most lets with
    //      `insts <= 1` will be inlined immediately.
    case let @ Let(vd, e, b) =>
      simplifyCache.get(let)
        .filter(_._1.subsumes(path))
        .map(p => (p._2, p._3))
        .getOrElse {
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

          val (lete, letp) = if (
            (((!inLambda && pe) || (inLambda && realPE && !containsLambda)) && insts <= 1) ||
            (!inLambda && immediateCall && insts == 1)
          ) {
            simplify(replaceFromSymbols(Map(vd -> re), rb), path)
          } else {
            val let = Let(vd, re, rb)
            re match {
              case l: Lambda =>
                val inlined = inlineLambdas(let)
                if (inlined != let) simplify(inlined, path)
                else (let, pe && pb)
              case _ => (let, pe && pb)
            }
          }

          simplifyCache(let) = (path, lete, letp)
          (lete, letp)
        }

    case Equals(e1: Literal[_], e2: Literal[_]) =>
      (BooleanLiteral(e1 == e2), true)

    case Equals(e1: Terminal, e2: Terminal) if e1 == e2 =>
      (BooleanLiteral(true), true)

    case Not(e) =>
      val (re, pe) = simplify(e, path)
      (not(re), pe)

    case FunctionInvocation(id, tps, args) =>
      val (rargs, pargs) = args.map(simplify(_, path)).unzip
      (FunctionInvocation(id, tps, rargs), pargs.foldLeft(isPureFunction(id))(_ && _))

    case Tuple(es)           => simplifyAndCons(es, path, tupleWrap)
    case UMinus(t)           => simplifyAndCons(Seq(t), path, es => uminus(es.head))
    case Plus(l, r)          => simplifyAndCons(Seq(l, r), path, es => plus(es(0), es(1)))
    case Minus(l, r)         => simplifyAndCons(Seq(l, r), path, es => minus(es(0), es(1)))
    case Times(l, r)         => simplifyAndCons(Seq(l, r), path, es => times(es(0), es(1)))
    case Forall(args, body)  => simplifyAndCons(Seq(body), path, es => simpForall(args, es.head))

    case Application(e, es)  => simplify(e, path) match {
      case (l: Lambda, _) =>
        val (res, _) = es.map(simplify(_, path)).unzip
        simplify(application(l, res), path)

      case (Assume(pred, l: Lambda), _) =>
        val (res, _) = es.map(simplify(_, path)).unzip
        simplify(assume(pred, application(l, res)), path)

      case (re, _) =>
        (application(re, es.map(simplify(_, path)._1)), opts.assumeChecked)
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

