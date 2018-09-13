/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package transformers

import utils._

import scala.util.DynamicVariable
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait SimplifierWithCNFPath extends SimplifierWithPC { self =>
  import trees._
  import symbols._
  import exprOps.{trees => _, _}
  import dsl._

  class CNFPath private[SimplifierWithCNFPath] (
    private[SimplifierWithCNFPath] val exprSubst: Bijection[Variable, Expr],
    private[SimplifierWithCNFPath] val boolSubst: Map[Variable, Expr],
    private[SimplifierWithCNFPath] val conditions: Set[Expr],
    private[SimplifierWithCNFPath] val cnfCache: MutableMap[Expr, Seq[Expr]],
    private[SimplifierWithCNFPath] val simpCache: MutableMap[Expr, Set[Expr]]
  ) extends PathLike[CNFPath] with SolvingPath {

    override def in(that: SimplifierWithPC {
      val trees: self.trees.type
      val symbols: self.symbols.type
    }): that.Env = {
      val thatCnf = that.asInstanceOf[SimplifierWithCNFPath {
        val trees: self.trees.type
        val symbols: self.symbols.type
      }]
      new thatCnf.CNFPath(
        exprSubst.clone,
        boolSubst,
        conditions,
        cnfCache.clone,
        simpCache.clone
      ).asInstanceOf[that.Env]
    }

    def subsumes(that: CNFPath): Boolean =
      (conditions subsetOf that.conditions) &&
      (exprSubst.forall { case (k, e) => that.exprSubst.getB(k).exists(_ == e) }) &&
      (boolSubst.forall { case (k, e) => that.boolSubst.get(k).exists(_ == e) })

    private def unexpandLets(e: Expr, exprSubst: Bijection[Variable, Expr] = exprSubst): Expr = {
      postMap(exprSubst.getA)(e)
    }

    def implies(e: Expr) = {
      val TopLevelOrs(es) = unexpandLets(e)
      conditions contains orJoin(es.distinct.sortBy(_.hashCode))
    }

    override def expand(e: Expr): Expr = e match {
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
      case Or(es) =>
        val esCnf = es.map(cnf)
        if (esCnf.map(_.size).product > 10) Seq(e)
        else esCnf.foldLeft(Seq(BooleanLiteral(false): Expr)) {
          case (clauses, es) => es.flatMap(e => clauses.map(c => or(e, c)))
        }
      case Implies(l, r) => cnf(or(not(l), r))
      case IfExpr(c, t, e) => cnf(and(trees.implies(c, t), trees.implies(not(c), e)))
      case Not(neg) => neg match {
        case And(es) => cnf(orJoin(es.map(not)))
        case Or(es) => cnf(andJoin(es.map(not)))
        case Implies(l, r) => cnf(and(l, not(r)))
        case IfExpr(c, t, e) => cnf(and(trees.implies(c, not(t)), trees.implies(not(c), not(e))))
        case Not(e) => cnf(e)
        case BooleanLiteral(b) => Seq(BooleanLiteral(!b))
        case _ => Seq(e)
      }
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
      } else if (isSubtypeOf(vd.getType, BooleanType())) {
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

    override def negate =
      new CNFPath(exprSubst, boolSubst, Set(), cnfCache, simpCache) withCond not(and(conditions.toSeq: _*))

    def asString(implicit opts: PrinterOptions): String = andJoin(conditions.toSeq.sortBy(_.hashCode)).asString

    override def toString = asString(PrinterOptions.fromContext(Context.printNames))
  }

  implicit object CNFPath extends PathProvider[CNFPath] {
    def empty = new CNFPath(new Bijection[Variable, Expr], Map.empty, Set.empty, MutableMap.empty, MutableMap.empty)
  }

  type Env = CNFPath

  // @nv: note that we make sure the initial env is fresh each time
  //      (since aggressive caching of cnf computations is taking place)
  def initEnv: CNFPath = CNFPath.empty

  private class SimplificationCache(cache: Cache[Expr, (Set[Expr], Map[ValDef, Expr], Expr, Boolean)]) {
    private def normalize(expr: Expr, path: CNFPath): (Expr, Set[Expr], Map[ValDef, Expr], Map[ValDef, ValDef]) = {
      val subst: MutableMap[ValDef, ValDef] = MutableMap.empty
      val bindings: MutableMap[ValDef, Expr] = MutableMap.empty

      val transformer = new SelfTreeTransformer {
        private var localCounter = 0
        override def transform(vd: ValDef): ValDef = subst.getOrElse(vd, {
          path.exprSubst.getB(vd.toVariable).orElse(path.boolSubst.get(vd.toVariable)) match {
            case Some(expr) =>
              localCounter = localCounter + 1
              val newVd = vd.copy(id = new Identifier("x", localCounter, localCounter))
              bindings(newVd) = transform(expr)
              newVd
            case None => vd
          }
        })
      }

      val newExpr = transformer.transform(expr)
      val mapping = subst.toMap
      val newConds = path.conditions.map(applySubst(mapping, _))
      (newExpr, newConds, bindings.toMap, mapping)
    }

    private def applySubst(subst: Map[ValDef, ValDef], expr: Expr): Expr = new SelfTreeTransformer {
      override def transform(vd: ValDef): ValDef = subst.getOrElse(vd, vd)
    }.transform(expr)

    def cached(e: Expr, path: CNFPath)(body: => (Expr, Boolean)): (Expr, Boolean) = {
      val (normalized, conds, bindings, subst) = normalize(e, path)

      cache.get(normalized)
        .filter { case (cConds, cBindings, _, _) =>
          (conds subsetOf cConds) &&
          bindings.forall { case (k, v) => cBindings.get(k) == Some(v) }
        }
        .map { case (_, _, re, pe) => (applySubst(subst.map(_.swap), re), pe) }
        .getOrElse {
          val (re, pe) = body
          cache(e) = (conds, bindings, applySubst(subst, re), pe)
          (re, pe)
        }
    }
  }

  private val recentCache = new SimplificationCache(new LruCache(100))

  override protected def simplify(e: Expr, path: CNFPath): (Expr, Boolean) = e match {
    // @nv: Simplifying lets can lead to exponential simplification cost.
    //      The `recentCache` greatly reduces the cost of simplifying lets but
    //      there are still corner cases that will make this expensive.
    //      In `assumeChecked` mode, the cost should be lower as most lets with
    //      `insts <= 1` will be inlined immediately.
    case let @ Let(vd, e, b) => recentCache.cached(let, path)(super.simplify(let, path))
    case _ => super.simplify(e, path)
  }
}

