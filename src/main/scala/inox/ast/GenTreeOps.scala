/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package ast

import utils._

/** A type that pattern matches agains a type of `Sources` and extracts its components,
  * and a builder that given a set of `Target` components, reconstructs a `Target` tree
  * that corresponds to the initially deconstructed tree.
  *
  * @tparam Source The type of the tree to deconstruct
  * @tparam Target The type of the tree to reconstruct
  */
trait TreeExtractor {
  protected val s: Trees
  protected val t: Trees

  type Source <: s.Tree
  type Target <: t.Tree
  def unapply(e: Source): Option[(Seq[Source], Seq[Target] => Target)]
}

/** Generic tree traversals based on a deconstructor of a specific tree type
  *
  * @tparam Source The type of the tree to deconstruct
  * @tparam Target The type of the tree to reconstruct
  */
trait GenTreeOps { self =>
  protected val sourceTrees: Trees
  protected val targetTrees: Trees

  type Source <: sourceTrees.Tree
  type Target <: targetTrees.Tree

  /** An extractor for [[Source]]*/
  val Deconstructor: TreeExtractor {
    val s: self.sourceTrees.type
    val t: self.targetTrees.type
    type Source = self.Source
    type Target = self.Target
  }

  /* ========
   * Core API
   * ========
   *
   * All these functions should be stable, tested, and used everywhere. Modify
   * with care.
   */

  /** Does a right tree fold
    *
    * A right tree fold applies the input function to the subnodes first (from left
    * to right), and combine the results along with the current node value.
    *
    * @param f a function that takes the current node and the seq
    *        of results form the Sources.
    * @param e The value on which to apply the fold.
    * @return The expression after applying `f` on all Sources.
    * @note the computation is lazy, hence you should not rely on side-effects of `f`
    */
  def fold[T](f: (Source, Seq[T]) => T)(e: Source): T = {
    val rec = fold(f) _
    val Deconstructor(es, _) = e

    //Usages of views makes the computation lazy. (which is useful for
    //contains-like operations)
    f(e, es.view.map(rec))
  }


  /** Pre-traversal of the tree.
    *
    * Invokes the input function on every node '''before''' visiting
    * children. Traverse children from left to right Sources.
    *
    * e.g.
    * {{{
    *   Add(a, Minus(b, c))
    * }}}
    * will yield, in order:
    * {{{
    *   f(Add(a, Minus(b, c))); f(a); f(Minus(b, c)); f(b); f(c)
    * }}}
    *
    * @param f a function to apply on each node of the expression
    * @param e the expression to traverse
    */
  def preTraversal(f: Source => Unit)(e: Source): Unit = {
    val rec = preTraversal(f) _
    val Deconstructor(es, _) = e
    f(e)
    es.foreach(rec)
  }

  /** Post-traversal of the tree.
    *
    * Invokes the input function on every node '''after''' visiting
    * children.
    *
    * e.g.
    * {{{
    *   Add(a, Minus(b, c))
    * }}}
    * will yield, in order:
    * {{{
    *   f(a), f(b), f(c), f(Minus(b, c)), f(Add(a, Minus(b, c)))
    * }}}
    *
    * @param f a function to apply on each node of the expression
    * @param e the expression to traverse
    */
  def postTraversal(f: Source => Unit)(e: Source): Unit = {
    val rec = postTraversal(f) _
    val Deconstructor(es, _) = e
    es.foreach(rec)
    f(e)
  }

  /** Pre-transformation of the tree.
    *
    * Takes a partial function of replacements and substitute
    * '''before''' recursing down the trees.
    *
    * Supports two modes :
    *
    *   - If applyRec is false (default), will only substitute once on each level.
    *
    *   e.g.
    *   {{{
    *     Add(a, Minus(b, c)) with replacements: Minus(b,c) -> d, b -> e, d -> f
    *   }}}
    *   will yield:
    *   {{{
    *     Add(a, d)   // And not Add(a, f) because it only substitute once for each level.
    *   }}}
    *
    *   - If applyRec is true, it will substitute multiple times on each level:
    *
    *   e.g.
    *   {{{
    *   Add(a, Minus(b, c)) with replacements: Minus(b,c) -> d, b -> e, d -> f
    *   }}}
    *   will yield:
    *   {{{
    *   Add(a, f)
    *   }}}
    *
    * @note The mode with applyRec true can diverge if f is not well formed
    */
  def preMap(f: Source => Option[Source], applyRec : Boolean = false)(e: Source): Target = {
    def g(t: Source, u: Unit): (Option[Source], Unit) = (f(t), ())
    preMapWithContext[Unit](g, applyRec)(e, ())
  }
  
  
  /** Post-transformation of the tree.
    *
    * Takes a partial function of replacements.
    * Substitutes '''after''' recurring down the trees.
    *
    * Supports two modes :
    *
    *   - If applyRec is false (default), will only substitute once on each level.
    *   e.g.
    *   {{{
    *     Add(a, Minus(b, c)) with replacements: Minus(b,c) -> z, Minus(e,c) -> d, b -> e
    *   }}}
    *   will yield:
    *   {{{
    *     Add(a, Minus(e, c))
    *   }}}
    *
    *   - If applyRec is true, it will substitute multiple times on each level:
    *   e.g.
    *   {{{
    *     Add(a, Minus(b, c)) with replacements: Minus(e,c) -> d, b -> e, d -> f
    *   }}}
    *   will yield:
    *   {{{
    *     Add(a, f)
    *   }}}
    *
    * @note The mode with applyRec true can diverge if f is not well formed (i.e. not convergent)
    */
  def postMap(f: Target => Option[Target], applyRec : Boolean = false)(e: Source): Target = {
    val rec = postMap(f, applyRec) _

    val Deconstructor(es, builder) = e
    val newEs = es.map(rec)
    val newV: Target = {
      if ((newEs zip es).exists { case (bef, aft) => aft ne bef } || (sourceTrees ne targetTrees)) {
        builder(newEs).copiedFrom(e)
      } else {
        e.asInstanceOf[Target]
      }
    }

    if (applyRec) {
      // Apply f as long as it returns Some()
      fixpoint { e : Target => f(e) getOrElse e } (newV)
    } else {
      f(newV) getOrElse newV
    }
  }

  /** Applies functions and combines results in a generic way
    *
    * Start with an initial value, and apply functions to nodes before
    * and after the recursion in the children. Combine the results of
    * all children and apply a final function on the resulting node.
    *
    * @param pre a function applied on a node before doing a recursion in the children
    * @param post a function applied to the node built from the recursive application to
                  all children
    * @param combiner a function to combine the resulting values from all children with
                      the current node
    * @param init the initial value
    * @param expr the expression on which to apply the transform
    * @see [[simpleTransform]]
    * @see [[simplePreTransform]]
    * @see [[simplePostTransform]]
    */
  def genericTransform[C](pre:  (Source, C) => (Source, C),
                          post: (Target, C) => (Target, C),
                          combiner: (Target, Seq[C]) => C)(init: C)(expr: Source) = {

    def rec(eIn: Source, cIn: C): (Target, C) = {

      val (expr, ctx) = pre(eIn, cIn)
      val Deconstructor(es, builder) = expr
      val (newExpr, newC) = {
        val (nes, cs) = es.map{ rec(_, ctx)}.unzip
        val newE = builder(nes).copiedFrom(expr)

        (newE, combiner(newE, cs))
      }

      post(newExpr, newC)
    }

    rec(expr, init)
  }

  def noCombiner(e: Target, subCs: Seq[Unit]) = ()
  def noTransformer[C](e: Source, c: C) = (e, c)

  /** A [[genericTransform]] with the trivial combiner that returns () */
  def simpleTransform(pre: Source => Source, post: Target => Target)(tree: Source) = {
    val newPre  = (e: Source, c: Unit) => (pre(e), ())
    val newPost = (e: Target, c: Unit) => (post(e), ())

    genericTransform[Unit](newPre, newPost, noCombiner)(())(tree)._1
  }

  /** A [[simpleTransform]] without a post-transformation */
  def simplePreTransform(pre: Source => Source)(tree: Source) = {
    val newPre  = (e: Source, c: Unit) => (pre(e), ())

    genericTransform[Unit](newPre, (_, _), noCombiner)(())(tree)._1
  }

  /** A [[simpleTransform]] without a pre-transformation */
  def simplePostTransform(post: Target => Target)(tree: Source) = {
    val newPost = (e: Target, c: Unit) => (post(e), ())

    genericTransform[Unit]((e,c) => (e, None), newPost, noCombiner)(())(tree)._1
  }



  /** Pre-transformation of the tree, with a context value from "top-down".
    *
    * Takes a partial function of replacements.
    * Substitutes '''before''' recursing down the trees. The function returns
    * an option of the new value, as well as the new context to be used for
    * the recursion in its children. The context is "lost" when going back up,
    * so changes made by one node will not be see by its siblings.
    */
  def preMapWithContext[C](f: (Source, C) => (Option[Source], C), applyRec: Boolean = false)
                          (e: Source, c: C): Target = {

    def rec(expr: Source, context: C): Target = {

      val (newV, newCtx) = {
        if(applyRec) {
          var ctx = context
          val finalV = fixpoint{ e: Source => {
            val res = f(e, ctx)
            ctx = res._2
            res._1.getOrElse(e)
          }} (expr)
          (finalV, ctx)
        } else {
          val res = f(expr, context)
          (res._1.getOrElse(expr), res._2)
        }
      }

      val Deconstructor(es, builder) = newV
      val newEs = es.map(e => rec(e, newCtx))

      if ((newEs zip es).exists { case (bef, aft) => aft ne bef } || (sourceTrees ne targetTrees)) {
        builder(newEs).copiedFrom(newV)
      } else {
        newV.asInstanceOf[Target]
      }

    }

    rec(e, c)
  }

  def preFoldWithContext[C](f: (Source, C) => C, combiner: (Source, C, Seq[C]) => C)
                           (e: Source, c: C): C = {

    def rec(eIn: Source, cIn: C): C = {
      val ctx = f(eIn, cIn)
      val Deconstructor(es, _) = eIn
      val cs = es.map{ rec(_, ctx) }
      combiner(eIn, ctx, cs)
    }

    rec(e, c)
  }

  /*
   * =============
   * Auxiliary API
   * =============
   *
   * Convenient methods using the Core API.
   */

  /** Checks if the predicate holds in some sub-expression */
  def exists(matcher: Source => Boolean)(e: Source): Boolean = {
    fold[Boolean]({ (e, subs) =>  matcher(e) || subs.contains(true) } )(e)
  }

  /** Collects a set of objects from all sub-expressions */
  def collect[T](matcher: Source => Set[T])(e: Source): Set[T] = {
    fold[Set[T]]({ (e, subs) => matcher(e) ++ subs.flatten } )(e)
  }

  def collectPreorder[T](matcher: Source => Seq[T])(e: Source): Seq[T] = {
    fold[Seq[T]]({ (e, subs) => matcher(e) ++ subs.flatten } )(e)
  }

  /** Returns a set of all sub-expressions matching the predicate */
  def filter(matcher: Source => Boolean)(e: Source): Set[Source] = {
    collect[Source] { e => Set(e) filter matcher }(e)
  }

  /** Counts how many times the predicate holds in sub-expressions */
  def count(matcher: Source => Int)(e: Source): Int = {
    fold[Int]({ (e, subs) => matcher(e) + subs.sum } )(e)
  }

  /** Replaces bottom-up sub-expressions by looking up for them in a map */
  def replace(substs: Map[Target, Target], expr: Source): Target = {
    postMap(substs.lift)(expr)
  }

  /** Computes the size of a tree */
  def formulaSize(t: Source): Int = {
    val Deconstructor(ts, _) = t
    ts.map(formulaSize).sum + 1
  }

  /** Computes the depth of the tree */
  def depth(e: Source): Int = {
    fold[Int]{ (_, sub) => 1 + (0 +: sub).max }(e)
  }

  /** Given a tree `toSearch` present in `treeToLookInto`, if `treeToLookInto` has the same shape as `treeToExtract`,
   *  returns the matching expression in `treeToExtract``.*/
  def lookup[T](checker: Source => Boolean, toExtract: Source => T)(treeToLookInto: Source, treeToExtract: Source): Option[T] = {
    if(checker(treeToLookInto)) return Some(toExtract(treeToExtract))
    
    val Deconstructor(childrenToLookInto, _) = treeToLookInto
    val Deconstructor(childrenToReturn, _) = treeToExtract
    if(childrenToLookInto.size != childrenToReturn.size) return None
    for((l, r) <- childrenToLookInto.zip(childrenToReturn)) {
      lookup(checker, toExtract)(l, r) match {
        case s@Some(n) => return s
        case _ =>
      }
    }
    None
  }

  object Same {
    def unapply(tt: (Source, Target))
               (implicit ev1: Source =:= Target, ev2: Target =:= Source): Option[(Source, Target)] = {
      val Deconstructor(es1, recons1) = tt._1
      val Deconstructor(es2, recons2) = ev2(tt._2)

      if (es1.size == es2.size && scala.util.Try(recons2(es1.map(ev1))).toOption == Some(ev2(tt._1))) {
        Some(tt)
      } else {
        None
      }
    }
  }

}
