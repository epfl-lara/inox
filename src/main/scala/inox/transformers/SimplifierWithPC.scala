/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

import utils._
import scala.collection.mutable.{Map => MutableMap}

trait SimplifierWithPC extends TransformerWithPC { self =>
  import trees._
  import symbols._
  import exprOps._
  import dsl._

  val opts: solvers.PurityOptions

  class CNFPath private(
    private val exprSubst: Bijection[Variable, Expr],
    private val boolSubst: Map[Variable, Seq[Expr]],
    private val conditions: Set[Expr],
    private val cnfCache: MutableMap[Expr, Seq[Expr]],
    private val simpCache: MutableMap[Expr, Seq[Expr]]) extends PathLike[CNFPath] {

    import exprOps._

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

    private def getClauses(e: Expr): Seq[Expr] = simpCache.getOrElseUpdate(e, {
      val (preds, newE) = liftAssumptions(simplifyLets(unexpandLets(e)))
      val expr = andJoin(newE +: preds)
      simpCache.getOrElseUpdate(expr, {
        val clauses = new scala.collection.mutable.ListBuffer[Expr]
        for (cl <- cnf(expr)) clauses ++= (simplify(cl) match {
          case v: Variable =>
            boolSubst.getOrElse(v, Seq(v))

          case Not(v: Variable) =>
            boolSubst.getOrElse(v, Seq(v)).foldLeft(Seq(BooleanLiteral(false): Expr)) {
              case (ors, TopLevelOrs(es)) => es.flatMap(e => ors.map(d => or(d, not(e))))
            }

          case Or(disjuncts) =>
            disjuncts.foldLeft(Seq(BooleanLiteral(false): Expr)) {
              case (ors, d) => d match {
                case v: Variable => boolSubst.getOrElse(v, Seq(v)).flatMap {
                  vdisj => ors.map(d => or(d, vdisj))
                }

                case Not(v: Variable) => boolSubst.getOrElse(v, Seq(v)).foldLeft(ors) {
                  case (ors, TopLevelOrs(es)) => es.flatMap(e => ors.map(d => or(d, not(e))))
                }

                case e => ors.map(d => or(d, e))
              }
            }

          case e => Seq(e)
        })

        val clauseSet = clauses.map { case TopLevelOrs(es) => orJoin(es.distinct.sortBy(_.hashCode)) }.toSet

        clauseSet.map { case TopLevelOrs(es) =>
          val eSet = es.toSet
          if (es.exists(e => conditions(e) || (eSet contains not(e)))) {
            BooleanLiteral(true)
          } else if (es.size > 1 && es.exists(e => clauseSet(e))) {
            BooleanLiteral(true)
          } else {
            orJoin(es.filter(e => !clauseSet(not(e)) && !conditions(not(e))))
          }
        }.toSeq.filterNot(_ == BooleanLiteral(true))
      })
    })

    def withBinding(p: (ValDef, Expr)) = {
      val (vd, expr) = p
      if (formulaSize(expr) > 20) {
        this
      } else if (vd.tpe == BooleanType) {
        new CNFPath(exprSubst, boolSubst + (vd.toVariable -> getClauses(expr)), conditions, cnfCache, simpCache)
      } else {
        val newSubst = exprSubst.clone += (vd.toVariable -> unexpandLets(expr))
        val newBools = boolSubst.mapValues(_.map(unexpandLets(_, newSubst)))
        val newConds = conditions.map(unexpandLets(_, newSubst))

        for ((k, v) <- cnfCache) {
          val newK = unexpandLets(k, newSubst)
          val newV = v.map(unexpandLets(_, newSubst))
          cnfCache += newK -> newV
        }

        for ((k, v) <- simpCache) {
          val newK = unexpandLets(k, newSubst)
          val newV = v.map(unexpandLets(_, newSubst))
          simpCache += newK -> newV
        }

        new CNFPath(newSubst, newBools, newConds, cnfCache, simpCache)
      }
    }

    def withCond(e: Expr) = if (formulaSize(e) > 20) this else {
      val clauses = getClauses(e)
      val clauseSet = clauses.toSet
      val newConditions = conditions.flatMap { case clause @ TopLevelOrs(es) =>
        val newClause = orJoin(es.filterNot(e => clauseSet contains not(e)))
        if (newClause != clause) cnf(newClause) else Seq(clause)
      }

      val conds = newConditions ++ clauseSet - BooleanLiteral(true)

      new CNFPath(exprSubst, boolSubst, conds, cnfCache, simpCache)
    }

    def merge(that: CNFPath) = new CNFPath(
      exprSubst.clone ++= that.exprSubst,
      boolSubst ++ that.boolSubst,
      conditions ++ that.conditions,
      cnfCache ++= that.cnfCache,
      simpCache ++= that.simpCache
    )

    def negate = new CNFPath(exprSubst, boolSubst, Set(), cnfCache, simpCache) withConds conditions.map(not)

    override def toString = conditions.toString
  }

  implicit object CNFPath extends PathProvider[CNFPath] {
    def empty = new CNFPath(new Bijection[Variable, Expr], Map.empty, Set.empty, MutableMap.empty, MutableMap.empty)
    def apply(path: Path) = path.elements.foldLeft(empty) {
      case (path, Left(p)) => path withBinding (p._1 -> transform(p._2, path))
      case (path, Right(c)) => path withCond (transform(c, path))
    }
  }

  type Env = CNFPath

  // @nv: note that we make sure the initial env is fresh each time
  //      (since aggressive caching of cnf computations is taking place)
  def initEnv: CNFPath = CNFPath.empty

  private[this] var stack: List[Int] = Nil
  private[this] var purity: List[Boolean] = Nil

  private val pureCache: MutableMap[Identifier, Boolean] = MutableMap.empty

  private def isPureFunction(id: Identifier): Boolean = opts.assumeChecked || (pureCache.get(id) match {
    case Some(b) => b
    case None =>
      val fd = getFunction(id)
      if (transitivelyCalls(fd, fd)) {
        pureCache += id -> false
        false
      } else {
        pureCache += id -> true
        if (isPure(fd.fullBody, CNFPath.empty)) {
          true
        } else {
          pureCache += id -> false
          transitiveCallers(fd).foreach(fd => pureCache += fd.id -> false)
          false
        }
      }
  })

  private def isInstanceOf(e: Expr, tpe: ADTType, path: CNFPath): Option[Boolean] = {
    val tadt = tpe.getADT
    if (tadt.definition.isSort) {
      Some(true)
    } else if (path contains IsInstanceOf(e, tpe)) {
      Some(true)
    } else if (tadt.toConstructor.sort.isDefined) {
      val tsort = tadt.toConstructor.sort.get
      val alts = (tsort.constructors.toSet - tadt).map(_.toType)

      if (alts exists (tpe => path contains IsInstanceOf(e, tpe))) {
        Some(false)
      } else if (alts forall (tpe => path contains Not(IsInstanceOf(e, tpe)))) {
        Some(true)
      } else {
        None
      }
    } else {
      None
    }
  }

  def isPure(e: Expr, path: CNFPath): Boolean = simplify(e, path)._2

  def simplify(e: Expr, path: CNFPath): (Expr, Boolean) = e match {
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

    case IsInstanceOf(ADT(tpe1, args), tpe2: ADTType) if !tpe2.getADT.definition.isSort =>
      simplify((tpe1.getADT.toConstructor.fields zip args).foldRight(BooleanLiteral(tpe1.id == tpe2.id): Expr) {
        case ((vd, e), body) => Let(vd.freshen, e, body)
      }, path)

    case IsInstanceOf(e, tpe: ADTType) =>
      val (re, pe) = simplify(e, path)
      if (tpe.getADT.definition.isSort) {
        (BooleanLiteral(true), pe)
      } else isInstanceOf(re, tpe, path) match {
        case Some(b) => (BooleanLiteral(b), true)
        case None => (IsInstanceOf(re, tpe), pe)
      }

    case AsInstanceOf(e, tpe: ADTType) =>
      val (re, pe) = simplify(e, path)
      val tadt = tpe.getADT
      isInstanceOf(re, tpe, path) match {
        case Some(true) => (AsInstanceOf(re, tpe), pe)
        case _ => (AsInstanceOf(re, tpe), opts.assumeChecked)
      }

    case Let(vd, IfExpr(c1, t1, e1), IfExpr(c2, t2, e2)) if c1 == c2 =>
      simplify(IfExpr(c1, Let(vd, t1, t2), Let(vd, e1, e2)), path)

    case Let(vd, v: Variable, b) => simplify(replaceFromSymbols(Map(vd -> v), b), path)

    case Let(vd, ADT(tpe, es), b) if (opts.assumeChecked || !tpe.getADT.hasInvariant) && {
      val v = vd.toVariable
      def rec(e: Expr): Boolean = e match {
        case ADTSelector(`v`, id) => true
        case `v` => false
        case Operator(es, _) => es.forall(rec)
      }
      rec(b)
    } =>
      val tadt = tpe.getADT.toConstructor
      val vds = tadt.fields.map(_.freshen)
      val selectors = tadt.fields.map(f => ADTSelector(vd.toVariable, f.id))
      val selectorMap: Map[Expr, Expr] = (selectors zip vds.map(_.toVariable)).toMap
      simplify((vds zip es).foldRight(replace(selectorMap, b)) { case ((vd, e), b) => Let(vd, e, b) }, path)

    case Let(vd, e, b) =>
      val (re, pe) = simplify(e, path)
      val (rb, pb) = simplify(b, path withBinding (vd -> re))

      val v = vd.toVariable
      lazy val insts = count { case `v` => 1 case _ => 0 }(rb)
      lazy val inLambda = exists { case l: Lambda => variablesOf(l) contains v case _ => false }(rb)
      lazy val immediateCall = existsWithPC(rb) { case (`v`, path) => path.isEmpty case _ => false }
      lazy val realPE = opts match {
        case solvers.PurityOptions.Unchecked => pe
        case solvers.PurityOptions.TotalFunctions => pe
        case _ =>
          val simp = simplifier(solvers.PurityOptions.Unchecked)
          simp.isPure(e, path.asInstanceOf[simp.CNFPath])
      }

      if (
        (((!inLambda && pe) || (inLambda && realPE)) && insts <= 1) ||
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

    case ADT(tpe, args)      => simplifyAndCons(args, path, adt(tpe, _))
    case Tuple(es)           => simplifyAndCons(es, path, tupleWrap)
    case ADTSelector(e, sel) => simplifyAndCons(Seq(e), path, es => adtSelector(es.head, sel))
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
      stack = 0 :: stack
      val re = super.rec(e, path)
      val (rpure, rest) = purity.splitAt(stack.head)
      val pe = rpure.foldLeft(opts.assumeChecked || !isImpureExpr(re))(_ && _)
      stack = stack.tail
      purity = rest
      (re, pe)
  }

  private def simplifyAndCons(es: Seq[Expr], path: CNFPath, cons: Seq[Expr] => Expr): (Expr, Boolean) = {
    val (res, pes) = es.map(simplify(_, path)).unzip
    val re = cons(res)
    val pe = pes.foldLeft(opts.assumeChecked || !isImpureExpr(re))(_ && _)
    (re, pe)
  }

  override protected def rec(e: Expr, path: CNFPath): Expr = {
    stack = if (stack.isEmpty) Nil else (stack.head + 1) :: stack.tail
    val (re, pe) = simplify(e, path)
    purity = if (stack.isEmpty) purity else pe :: purity
    re
  }
}

