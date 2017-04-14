/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package transformers

import scala.collection.mutable.{Map => MutableMap}

trait SimplifierWithPC extends TransformerWithPC { self =>
  import trees._
  import symbols._
  import exprOps._
  import dsl._

  type Env = CNFPath

  private[this] var purity: Boolean = true

  private val pureCache: MutableMap[Identifier, Boolean] = MutableMap.empty

  private def isPureFunction(id: Identifier): Boolean = pureCache.get(id) match {
    case Some(b) => b
    case None =>
      pureCache += id -> true
      val fd = getFunction(id)
      if (isPure(fd.fullBody, CNFPath.empty)) {
        true
      } else {
        pureCache += id -> false
        transitiveCallers(fd).foreach(fd => pureCache += fd.id -> false)
        false
      }
  }

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
    case c: Choose => (c, false)

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
        (Assume(BooleanLiteral(false), rb), false)
      case (rp, _) =>
        val (rb, _) = simplify(body, path withCond rp)
        (Assume(rp, rb), false)
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
        case _ => (AsInstanceOf(re, tpe), false)
      }

    case Let(vd, IfExpr(c1, t1, e1), IfExpr(c2, t2, e2)) if c1 == c2 =>
      simplify(IfExpr(c1, Let(vd, t1, t2), Let(vd, e1, e2)), path)

    case Let(vd, v: Variable, b) => simplify(replaceFromSymbols(Map(vd -> v), b), path)

    case Let(vd, ADT(tpe, es), b) if !tpe.getADT.hasInvariant && {
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
      val insts = count { case `v` => 1 case _ => 0 }(rb)
      if (
        (pe && insts <= 1) ||
        (insts == 1 && collectWithPaths[Variable] { case (path, `v`) if path.isEmpty => v }(rb).nonEmpty)
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
      (FunctionInvocation(id, tps, rargs), pargs.foldLeft(true)(_ && _) && isPureFunction(id))

    case ADT(tpe, args)      => simplifyAndCons(args, path, adt(tpe, _))
    case Tuple(es)           => simplifyAndCons(es, path, tupleWrap)
    case ADTSelector(e, sel) => simplifyAndCons(Seq(e), path, es => adtSelector(es.head, sel))
    case UMinus(t)           => simplifyAndCons(Seq(t), path, es => uminus(es.head))
    case Plus(l, r)          => simplifyAndCons(Seq(l, r), path, es => plus(es(0), es(1)))
    case Minus(l, r)         => simplifyAndCons(Seq(l, r), path, es => minus(es(0), es(1)))
    case Times(l, r)         => simplifyAndCons(Seq(l, r), path, es => times(es(0), es(1)))
    case Application(e, es)  => simplifyAndCons(e +: es, path, es => application(es.head, es.tail))
    case Forall(args, body)  => simplifyAndCons(Seq(body), path, es => simpForall(args, es.head))

    case _ =>
      val old = purity
      purity = true
      val re = super.rec(e, path)
      val pe = purity && !isImpureExpr(re)
      purity &&= old && pe
      (re, pe)
  }

  private def simplifyAndCons(es: Seq[Expr], path: CNFPath, cons: Seq[Expr] => Expr): (Expr, Boolean) = {
    val (res, pes) = es.map(simplify(_, path)).unzip
    (cons(res), pes.foldLeft(true)(_ && _))
  }

  override protected def rec(e: Expr, path: CNFPath): Expr = {
    purity = true
    val (re, _) = simplify(e, path)
    re
  }
}
