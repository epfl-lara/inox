/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait Paths { self: SymbolOps with TypeOps =>
  import trees._

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

    def apply(path: Seq[Expr])(implicit d: DummyImplicit): Path =
      new Path(path filterNot { _ == BooleanLiteral(true) } map Condition)
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
    extends Printable with PathLike[Path] {
    import Path.{ Element, CloseBound, OpenBound, Condition }

    private def :+(e: Element): Path = {
      e match {
        case CloseBound(vd, _) => assertNotInPath(vd)
        case OpenBound(vd) => assertNotInPath(vd)
        case Condition(_) => // no check
      }
      new Path(elements :+ e)
    }

    private def assertNotInPath(vd: ValDef): Unit = {
      val exprs = elements collect {
        case CloseBound(_, e) => e
        case Condition(e) => e
      }
      assert(exprs forall { e => !(exprOps.variablesOf(e) contains vd.toVariable) })
    }

    /** Add a binding to this [[Path]] */
    override def withBinding(p: (ValDef, Expr)): Path = this :+ CloseBound(p._1, p._2)

    /** Add a bound to this [[Path]], a variable being defined but to an unknown/arbitrary value. */
    override def withBound(b: ValDef): Path = this :+ OpenBound(b)

    /** Add a condition to this [[Path]] */
    override def withCond(e: Expr): Path = e match {
      case TopLevelAnds(es) if es.size > 1 => withConds(es)
      case Not(TopLevelOrs(es)) if es.size > 1 => withConds(es map not)
      case _ =>
        def replaceNeg(from: Expr)(to: Expr) = exprOps.replace(Map(not(from) -> BooleanLiteral(false)), to)

        val prefix: Seq[Element] = elements map {
          case Condition(c) => Condition(simplifyByConstructors(replaceNeg(e)(c)))
          case p => p
        }
        val last = Condition(simplifyByConstructors(conditions.foldLeft(e) { (acc, c) => replaceNeg(c)(acc) }))
        val newElements = (prefix :+ last) filter { _ != Condition(BooleanLiteral(true)) } // simplify path
        new Path(newElements)
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
      *
      * @see [[map(f:Paths\.this\.trees\.Expr=>Paths\.this\.trees\.Expr):Paths\.this\.Path* map]]
      *      for a map defined only on expressions
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
      val t = new TypeInstantiator(tps)
      new Path(elements map {
        case CloseBound(vd, e) => CloseBound(t transform vd, t transform e)
        case OpenBound(vd) => OpenBound(t transform vd)
        case Condition(c) => Condition(t transform c)
      })
    }

    /** Check if the path is empty
      *
      * A path is empty iff it contains no let-bindings and its path condition is trivial.
      */
    lazy val isEmpty = elements forall {
      case Condition(BooleanLiteral(true)) => true
      case _ => false
    }

    /** Returns the negation of a path
      *
      * Path negation requires folding the path into a proposition and negating it.
      * However, all external let-binders can be preserved in the resulting path, thus
      * avoiding let-binding dupplication in future path foldings.
      */
    override def negate: Path = {
      val (outers, rest) = elements span { !_.isInstanceOf[Condition] }
      new Path(outers) :+ Condition(not(fold[Expr](BooleanLiteral(true), let, trees.and(_, _))(rest)))
    }

    /** Returns a new path which depends ONLY on provided ids.
      *
      * Let-bindings obviously depend on some `id` if it corresponds to the bound
      * identifier. An expression depends on an `id` iff the identifier is
      * contained within the expression.
      *
      * This method makes little sense on its own and will typically be used from
      * within a fixpoint computation where the `ids` set is iteratively computed
      * by performing [[filterByIds]] calls on some (unchaning) base [[Path]].
      *
      * @see [https://github.com/epfl-lara/stainless/blob/master/src/main/scala/stainless/extraction/innerfuns/FunctionClosure.scala](
      *       FunctionClosure in stainless for an example usecase).
      */
    def filterByIds(ids: Set[Identifier]): Path = {
      def containsIds(ids: Set[Identifier])(e: Expr): Boolean = exprOps.exists {
        case Variable(id, _, _) => ids contains id
        case _ => false
      }(e)

      val newElements = elements filter {
        case CloseBound(vd, e) => (ids contains vd.id) || containsIds(ids)(e)
        case OpenBound(vd) => ids contains vd.id
        case Condition(e) => containsIds(ids)(e)
      }

      new Path(newElements)
    }

    /** Free variables within the path */
    lazy val freeVariables: Set[Variable] = {
      val allVars = elements. collect { case Condition(e) => e; case CloseBound(_, e) => e }
                            . flatMap { e => exprOps.variablesOf(e) }
      val boundVars = bounds map { _.toVariable }
      allVars.toSet -- boundVars
    }

    lazy val bindings: Seq[(ValDef, Expr)] = elements collect { case CloseBound(vd, e) => vd -> e }

    lazy val bounds: Seq[ValDef] = elements collect {
      case CloseBound(vd, _) => vd
      case OpenBound(vd) => vd
    }

    lazy val conditions: Seq[Expr] = elements collect { case Condition(e) => e }

    def isBound(id: Identifier): Boolean = bounds exists { _.id == id }

    /** Fold the path elements
      *
      * This function takes two combiner functions, one for let bindings and one
      * for proposition expressions.
      */
    private def fold[T](base: T, combineLet: (ValDef, Expr, T) => T, combineCond: (Expr, T) => T)
                       (elems: Seq[Element]): T = elems.foldRight(base) {
      case (CloseBound(vd, e), res) => combineLet(vd, e, res)
      case (Condition(e), res) => combineCond(e, res)
      case (OpenBound(_), res) => res // No combiner for OpenBound
    }

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
      val inner = fold[Expr](base, let, combine)(rest)
      fold[Expr](inner, let, (_,_) => scala.sys.error("Should never happen!"))(outers)
    }

    /** Folds the path into a conjunct with the expression `base` */
    def and(base: Expr) = distributiveClause(base, trees.and(_, _))

    /** Fold the path into an implication of `base`, namely `path ==> base` */
    def implies(base: Expr) = distributiveClause(base, trees.implies)

    /** Folds the path into an expression that shares the path's outer lets
      *
      * The folding shares all outer bindings in an wrapping sequence of
      * let-expressions. The inner condition is then passed as the first
      * argument of the `recons` function and must be shared out between
      * the reconstructions of `es` which will only feature the bindings
      * from the current path.
      *
      * This method is useful to reconstruct if-expressions or assumptions
      * where the condition can be added to the expression in a position
      * that implies further positions.
      */
    def withShared(es: Seq[Expr], recons: (Expr, Seq[Expr]) => Expr): Expr = {
      val (outers, rest) = elements span { !_.isInstanceOf[Condition] }
      val bindings = rest collect { case CloseBound(vd, e) => vd -> e }
      val cond = fold[Expr](BooleanLiteral(true), let, trees.and(_, _))(rest)

      def wrap(e: Expr): Expr = {
        val subst = bindings.map(p => p._1 -> p._1.toVariable.freshen).toMap
        val replace = exprOps.replaceFromSymbols(subst, _: Expr)
        bindings.foldRight(replace(e)) { case ((vd, e), b) => let(subst(vd).toVal, replace(e), b) }
      }

      val full = recons(cond, es.map(wrap))
      fold[Expr](full, let, (_, _) => scala.sys.error("Should never happen!"))(outers)
    }

    /** Folds the path into the associated boolean proposition */
    lazy val toClause: Expr = and(BooleanLiteral(true))

    /** Like [[toClause]] but doesn't simplify final path through constructors
      * from [[Constructors]] */
    lazy val fullClause: Expr = fold[Expr](BooleanLiteral(true), Let, And(_, _))(elements)

    override def equals(that: Any): Boolean = that match {
      case p: Path => elements == p.elements && bounds == p.bounds
      case _ => false
    }

    override def hashCode: Int = elements.hashCode

    override def toString = asString(PrinterOptions.fromContext(Context.printNames))
    def asString(implicit opts: PrinterOptions): String = fullClause.asString
  }
}
