/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait Paths { self: SymbolOps with TypeOps =>
  import trees._

  object Path {
    final type Element = Either[(ValDef, Expr), Expr]

    def empty: Path = new Path(Seq.empty)

    def apply(p: Expr): Path = p match {
      case Let(i, e, b) => new Path(Seq(Left(i -> e))) merge apply(b)
      case BooleanLiteral(true) => new Path(Seq.empty)
      case _ => new Path(Seq(Right(p)))
    }

    def apply(p: (ValDef, Expr)): Path = new Path(Seq(Left(p)))

    def apply(path: Seq[Expr]): Path = new Path(path.filterNot(_ == BooleanLiteral(true)).map(Right(_)))
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
  class Path private(private[ast] val elements: Seq[Path.Element]) extends Printable {
    import Path.Element

    /** Add a binding to this [[Path]] */
    def withBinding(p: (ValDef, Expr)) = {
      def exprOf(e: Element) = e match { case Right(e) => e; case Left((_, e)) => e }
      val (before, after) = elements span (el => !exprOps.variablesOf(exprOf(el)).contains(p._1.toVariable))
      new Path(before ++ Seq(Left(p)) ++ after)
    }

    def withBindings(ps: Iterable[(ValDef, Expr)]) = {
      ps.foldLeft(this)( _ withBinding _ )
    }

    /** Add a condition to this [[Path]] */
    def withCond(e: Expr): Path = e match {
      case TopLevelAnds(es) if es.size > 1 => withConds(es)
      case Not(TopLevelOrs(es)) if es.size > 1 => withConds(es.map(not(_)))
      case _ =>
        val notE = not(e)
        val newElements = elements.map(_.right.map { e =>
          simplifyByConstructors(exprOps.replace(Map(notE -> BooleanLiteral(false)), e))
        }) :+ Right(simplifyByConstructors(conditions.foldLeft(e) { (e, c) =>
          exprOps.replace(Map(not(c) -> BooleanLiteral(false)), e)
        }))

        new Path(newElements.filterNot(_.right.exists(_ == BooleanLiteral(true))))
    }

    /** Add multiple conditions to this [[Path]] */
    def withConds(es: Iterable[Expr]) = es.foldLeft(this)((p, e) => p withCond e)

    /** Remove bound variables from this [[Path]]
      * @param ids the bound variables to remove
      */
    def --(vds: Set[ValDef]) = new Path(elements.filterNot(_.left.exists(p => vds(p._1))))

    /** Appends `that` path at the end of `this` */
    def merge(that: Path): Path = new Path((elements ++ that.elements).distinct)

    /** Appends `those` paths at the end of `this` */
    def merge(those: Traversable[Path]): Path = those.foldLeft(this)(_ merge _)

    /** Transforms all expressions inside the path
      *
      * Expressions in a path appear both on the right-hand side of let binders
      * and in boolean path conditions.
      *
      * @see [[map(fVal:Paths\.this\.trees\.ValDef=>Paths\.this\.trees\.ValDef,fExpr:Paths\.this\.trees\.Expr=>Paths\.this\.trees\.Expr):Paths\.this\.Path* map]]
      *      for a map that can transform bindings as well
      */
    def map(f: Expr => Expr) = new Path(elements.map(_.left.map { case (vd, e) => vd -> f(e) }.right.map(f)))

    /** Transforms both let bindings and expressions inside the path
      * 
      * The function `fVal` is applied to all values in [[bound]] and `fExpr` is applied
      * to both the bodies of the [[bindings]] as well as the [[conditions]].
      *
      * @see [[map(f:Paths\.this\.trees\.Expr=>Paths\.this\.trees\.Expr):Paths\.this\.Path* map]]
      *      for a map defined only on expressions
      */
    def map(fVal: ValDef => ValDef, fExpr: Expr => Expr) = new Path(
      elements.map(_.left.map { case (vd, e) => fVal(vd) -> fExpr(e) }.right.map(fExpr))
    )

    /** Instantiates type parameters within the path
      *
      * Type parameters within a path may appear both inside expressions and in
      * the type associated to a let binder.
      */
    def instantiate(tps: Map[TypeParameter, Type]) = {
      val t = new TypeInstantiator(tps)
      new Path(elements.map(_.left.map {
        case (vd, e) => t.transform(vd) -> t.transform(e)
      }.right.map(t.transform)))
    }

    /** Splits the path on predicate `p`
      *
      * The path is split into
      * 1. the sub-path containing all conditions that pass `p` (and all let-bindings), and
      * 2. the sequence of conditions that didn't pass `p`.
      */
    def partition(p: Expr => Boolean): (Path, Seq[Expr]) = {
      val (passed, failed) = elements.partition {
        case Right(e) => p(e)
        case Left(_) => true
      }

      (new Path(passed), failed.flatMap(_.right.toOption))
    }

    /** Check if the path is empty
      *
      * A path is empty iff it contains no let-bindings and its path condition is trivial.
      */
    def isEmpty = elements.forall {
      case Right(BooleanLiteral(true)) => true
      case _ => false
    }

    /** Returns the negation of a path
      *
      * Path negation requires folding the path into a proposition and negating it.
      * However, all external let-binders can be preserved in the resulting path, thus
      * avoiding let-binding dupplication in future path foldings.
      */
    def negate: Path = {
      val (outers, rest) = elements.span(_.isLeft)
      new Path(outers :+ Right(not(fold[Expr](BooleanLiteral(true), let, trees.and(_, _))(rest))))
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
        case Variable(id, _, _) => ids.contains(id)
        case _ => false
      }(e)
      
      val newElements = elements.filter{
        case Left((vd, e)) => ids.contains(vd.id) || containsIds(ids)(e)
        case Right(e) => containsIds(ids)(e)
      }
      new Path(newElements)
    }

    /** Free variables within the path */
    lazy val variables: Set[Variable] = fold[Set[Variable]](Set.empty,
      (vd, e, res) => res - vd.toVariable ++ exprOps.variablesOf(e), (e, res) => res ++ exprOps.variablesOf(e)
    )(elements)

    lazy val bindings: Seq[(ValDef, Expr)] = elements.collect { case Left(p) => p }
    lazy val bound = bindings map (_._1)
    lazy val conditions: Seq[Expr] = elements.collect { case Right(e) => e }

    def isBound(id: Identifier): Boolean = bindings.exists(p => p._1.id == id)

    /** Fold the path elements
      *
      * This function takes two combiner functions, one for let bindings and one
      * for proposition expressions.
      */
    private def fold[T](base: T, combineLet: (ValDef, Expr, T) => T, combineCond: (Expr, T) => T)
                       (elems: Seq[Element]): T = elems.foldRight(base) {
      case (Left((id, e)), res) => combineLet(id, e, res)
      case (Right(e), res) => combineCond(e, res)
    }

    /** Folds the path elements over a distributive proposition combinator [[combine]]
      * 
      * Certain combiners can be distributive over let-binding folds. Namely, one
      * requires that `combine(let a = b in e1, e2)` be equivalent to
      * `let a = b in combine(e1, e2)` (where a \not\in FV(e2)). This is the case for
      * - conjunction [[and]]
      * - implication [[implies]]
      */
    private def distributiveClause(base: Expr, combine: (Expr, Expr) => Expr): Expr = {
      val (outers, rest) = elements.span(_.isLeft)
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
      val (outers, rest) = elements.span(_.isLeft)
      val cond = fold[Expr](BooleanLiteral(true), let, trees.and(_, _))(rest)

      def wrap(e: Expr): Expr = {
        val bindings = rest.collect { case Left((vd, e)) => vd -> e }
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

    /** Folds the path into a boolean proposition where let-bindings are
      * replaced by equations.
      *
      * CAUTION: Should only be used once INSIDE the solver!!
      */
    lazy val toPath: Expr = andJoin(elements.map {
      case Left((id, e)) => Equals(id.toVariable, e)
      case Right(e) => e
    })

    override def equals(that: Any): Boolean = that match {
      case p: Path => elements == p.elements
      case _ => false
    }

    override def hashCode: Int = elements.hashCode

    override def toString = asString(PrinterOptions.fromContext(Context.printNames))
    def asString(implicit opts: PrinterOptions): String = fullClause.asString
  }
}
