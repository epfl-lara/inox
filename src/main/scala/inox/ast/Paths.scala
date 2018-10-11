/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import utils._

trait Paths { self: Trees =>

  trait PathLike[Self <: PathLike[Self]] { self: Self =>

    /** Add a binding to this `PathLike`. */
    def withBinding(p: (ValDef, Expr)): Self

    final def withBindings(ps: Iterable[(ValDef, Expr)]): Self = ps.foldLeft(self)(_ withBinding _)

    def withBound(b: ValDef): Self

    final def withBounds(bs: Iterable[ValDef]): Self = bs.foldLeft(self)(_ withBound _)

    /** Add a condition to this `PathLike`. */
    def withCond(e: Expr): Self

    /** Add multiple conditions to this `PathLike`. */
    final def withConds(es: Iterable[Expr]): Self = es.foldLeft(self)(_ withCond _)

    /** Appends `that` path at the end of `this`. */
    def merge(that: Self): Self

    /** Appends `those` paths at the end of `this`. */
    final def merge(those: Traversable[Self]): Self = those.foldLeft(self)(_ merge _)

    /** Returns the negation of this path. */
    def negate: Self
  }

  trait PathProvider[P <: PathLike[P]] {
    def empty: P

    def apply(path: Path): P = path.elements.foldLeft(empty) {
      case (env, Path.CloseBound(vd, e)) => env withBinding (vd -> e)
      case (env, Path.OpenBound(vd)) => env withBound vd
      case (env, Path.Condition(cond)) => env withCond cond
    }
  }

  implicit object Path extends PathProvider[Path] {
    sealed abstract class Element
    case class CloseBound(vd: ValDef, v: Expr) extends Element
    case class OpenBound(vd: ValDef) extends Element
    case class Condition(e: Expr) extends Element

    def empty: Path = new Path(Seq.empty)

    def apply(p: Element) = new Path(Seq(p))
    def apply(p: Seq[Element]) = new Path(p)

    def apply(p: Expr): Path = p match {
      case Let(i, e, b) => Path(CloseBound(i, e)) merge apply(b)
      case BooleanLiteral(true) => empty
      case _ => Path(Condition(p))
    }

    def apply(p: (ValDef, Expr)): Path = Path(CloseBound(p._1, p._2))
    def apply(vd: ValDef): Path = Path(OpenBound(vd))

    def apply(path: Seq[Expr])(implicit d: DummyImplicit): Path =
      new Path(path filterNot { _ == BooleanLiteral(true) } map Condition)

    /** Fold the path elements
      *
      * This function takes two combiner functions, one for let bindings and one
      * for proposition expressions.
      */
    def fold[T](base: T, combineLet: (ValDef, Expr, T) => T, combineCond: (Expr, T) => T)
               (elems: Seq[Element]): T = elems.foldRight(base) {
      case (CloseBound(vd, e), res) => combineLet(vd, e, res)
      case (Condition(e), res) => combineCond(e, res)
      case (OpenBound(_), res) => res
    }
  }

  /** Encodes path conditions
    *
    * Paths are encoded as an (ordered) series of let-bindings and boolean
    * propositions. A path is satisfiable iff all propositions are true
    * in the context of the provided let-bindings.
    *
    * This encoding enables let-bindings over types for which equality is
    * not defined, whereas an encoding of let-bindings with equalities
    * could introduce non-sensical equations.
    */
  class Path protected(val elements: Seq[Path.Element])
    extends Printable
       with PathLike[Path] {

    import Path._

    private def :+(e: Element) = new Path(elements :+ e)

    /** Add a binding to this [[Path]] */
    override def withBinding(p: (ValDef, Expr)) = {
      val (vd, value) = p
      assert(elements collect {
        case CloseBound(_, e) => e
        case Condition(e) => e
      } forall {
        e => !(exprOps.variablesOf(e) contains vd.toVariable)
      })
      this :+ CloseBound(vd, value)
    }

    /** Add a bound to this [[Path]], a variable being defined but to an unknown/arbitrary value. */
    override def withBound(b: ValDef) = {
      assert(elements collect {
        case CloseBound(_, e) => e
        case Condition(e) => e
      } forall {
        e => !(exprOps.variablesOf(e) contains b.toVariable)
      })
      this :+ OpenBound(b)
    }

    /** Add a condition to this [[Path]] */
    override def withCond(e: Expr): Path = e match {
      case BooleanLiteral(true) => this
      case TopLevelAnds(es) if es.size > 1 => withConds(es)
      case Not(TopLevelOrs(es)) if es.size > 1 => withConds(es map not)
      case _ => this :+ Condition(e)
    }

    /** Remove bound variables from this [[Path]]
      * @param ids the bound variables to remove
      */
    def --(vds: Set[ValDef]) = new Path(elements filter {
      case OpenBound(vd) if vds contains vd => false
      case CloseBound(vd, _) if vds contains vd => false
      case _ => true
    })

    /** Appends `that` path at the end of `this` */
    override def merge(that: Path): Path = new Path((elements ++ that.elements).distinct)

    /** Transforms both let bindings and expressions inside the path
      *
      * The function `fVal` is applied to all values in [[bound]] and `fExpr` is applied
      * to both the bodies of the [[bindings]] as well as the [[conditions]].
      */
    def map(fVal: ValDef => ValDef, fExpr: Expr => Expr) = new Path(elements map {
      case CloseBound(vd, e) => CloseBound(fVal(vd), fExpr(e))
      case OpenBound(vd) => OpenBound(fVal(vd))
      case Condition(c) => Condition(fExpr(c))
    })

    /** Instantiates type parameters within the path
      *
      * Type parameters within a path may appear both inside expressions and in
      * the type associated to a let binder.
      */
    def instantiate(tps: Map[TypeParameter, Type]) = {
      val t = new typeOps.TypeInstantiator(tps)
      new Path(elements map {
        case CloseBound(vd, e) => CloseBound(t transform vd, t transform e)
        case OpenBound(vd) => OpenBound(t transform vd)
        case Condition(c) => Condition(t transform c)
      })
    }

    /** Check if the path is empty
      *
      * A path is empty iff it contains no let-bindings and its path condition is trivial.
      * Note that empty paths may contain open bounds.
      */
    @inline def isEmpty: Boolean = _isEmpty.get
    private[this] val _isEmpty: Lazy[Boolean] = Lazy(elements forall {
      case Condition(BooleanLiteral(true)) => true
      case OpenBound(_) => true
      case _ => false
    })

    /** Returns the negation of a path
      *
      * Path negation requires folding the path into a proposition and negating it.
      * However, all external let-binders can be preserved in the resulting path, thus
      * avoiding let-binding dupplication in future path foldings.
      */
    override def negate: Path = _negate.get
    private[this] val _negate: Lazy[Path] = Lazy {
      val (outers, rest) = elements span { !_.isInstanceOf[Condition] }
      new Path(outers) :+ Condition(not(fold[Expr](BooleanLiteral(true), Let, self.and(_, _))(rest)))
    }

    /** Free variables within the path */
    @inline def freeVariables: Set[Variable] = _free.get
    private[this] val _free: Lazy[Set[Variable]] = Lazy {
      val allVars = elements
        .collect { case Condition(e) => e case CloseBound(_, e) => e }
        .flatMap { e => exprOps.variablesOf(e) }
      val boundVars = bound map { _.toVariable }
      allVars.toSet -- boundVars
    }

    /** Variables that aren't bound by a [[Path.CloseBound]]. */
    @inline def unboundVariables: Set[Variable] = _unbound.get
    private[this] val _unbound: Lazy[Set[Variable]] = Lazy {
      val allVars = elements
        .collect { case Condition(e) => e case CloseBound(_, e) => e }
        .flatMap { e => exprOps.variablesOf(e) }
      val boundVars = bindings map { _._1.toVariable }
      allVars.toSet -- boundVars
    }

    @inline def bindings: Seq[(ValDef, Expr)] = _bindings.get
    private[this] val _bindings: Lazy[Seq[(ValDef, Expr)]] =
      Lazy(elements.collect { case CloseBound(vd, e) => vd -> e })

    @inline def open: Seq[ValDef] = _open.get
    private[this] val _open: Lazy[Seq[ValDef]] =
      Lazy(elements.collect { case OpenBound(vd) => vd })

    @inline def closed: Seq[ValDef] = _closed.get
    private[this] val _closed: Lazy[Seq[ValDef]] =
      Lazy(elements.collect { case CloseBound(vd, _) => vd })

    @inline def bound: Seq[ValDef] = _bound.get
    private[this] val _bound: Lazy[Seq[ValDef]] =
      Lazy(elements.collect { case CloseBound(vd, _) => vd case OpenBound(vd) => vd })

    @inline def conditions: Seq[Expr] = _conditions.get
    private[this] val _conditions: Lazy[Seq[Expr]] =
      Lazy(elements.collect { case Condition(e) => e })

    def isBound(v: Variable): Boolean = bound exists { _.toVariable == v }

    /** Free variables of the input expression under the current path
      *
      * See [[freeVariables]] for some more details about _free_ variables
      */
    def freeOf(e: Expr): Set[Variable] = freeOf(exprOps.variablesOf(e))

    /** Free variables of the input variable set under the current path */
    def freeOf(vs: Set[Variable]): Set[Variable] = vs -- bound.map(_.toVariable) ++ freeVariables

    /** Unbound variables of the input expression under the current path
      *
      * See [[unboundVariables]] for some more details about _unbound_ variables
      */
    def unboundOf(e: Expr): Set[Variable] = unboundOf(exprOps.variablesOf(e))

    /** Unbound variables of the input variable set under the current path */
    def unboundOf(vs: Set[Variable]): Set[Variable] = vs -- closed.map(_.toVariable) ++ unboundVariables

    /** Folds the path elements over a distributive proposition combinator [[combine]]
      *
      * Certain combiners can be distributive over let-binding folds. Namely, one
      * requires that `combine(let a = b in e1, e2)` be equivalent to
      * `let a = b in combine(e1, e2)` (where a \not\in FV(e2)). This is the case for
      * - conjunction [[and]]
      * - implication [[implies]]
      *
      * NOTE Open bounds are lost; i.e. the generated expression can contain free variables.
      */
    private def distributiveClause(base: Expr, combine: (Expr, Expr) => Expr): Expr = {
      val (outers, rest) = elements span { !_.isInstanceOf[Condition] }
      val inner = fold[Expr](base, Let, combine)(rest)
      fold[Expr](inner, Let, (_,_) => scala.sys.error("Should never happen!"))(outers)
    }

    /** Folds the path into a conjunct with the expression `base` */
    def and(base: Expr) = distributiveClause(base, self.and(_, _))

    /** Fold the path into an implication of `base`, namely `path ==> base` */
    def implies(base: Expr) = distributiveClause(base, self.implies)

    /** Folds the path into the associated boolean proposition */
    @inline def toClause: Expr = _clause.get
    private[this] val _clause: Lazy[Expr] = Lazy(and(BooleanLiteral(true)))

    /** Like [[toClause]] but doesn't simplify final path through constructors
      * from [[Constructors]] */
    @inline def fullClause: Expr = _fullClause.get
    private[this] val _fullClause: Lazy[Expr] =
      Lazy(fold[Expr](BooleanLiteral(true), Let, And(_, _))(elements))

    override def equals(that: Any): Boolean = that match {
      case p: Path => elements == p.elements
      case _ => false
    }

    override def hashCode: Int = elements.hashCode

    override def toString = asString(PrinterOptions())
    def asString(implicit opts: PrinterOptions): String = fullClause.asString
  }
}
