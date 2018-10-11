/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import utils._
import transformers._

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

  /** A transformer from [[Source]] to [[Target]] */
  def transform[E](src: Source, env: E)(op: (Source, E, TransformerOp[Source, E, Target]) => Target): Target

  /** A traverser for [[Source]] trees */
  def traverse[E](src: Source, env: E)(op: (Source, E, TraverserOp[Source, E]) => Unit): Unit

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
    var stack: List[Int] = Nil
    var res: List[T] = Nil

    traverse(e, ()) { (e, env, op) =>
      if (stack.nonEmpty) stack = (stack.head + 1) :: stack.tail
      stack = 0 :: stack
      op.sup(e, env)
      val (rres, rest) = res.splitAt(stack.head)
      stack = stack.tail
      res = f(e, rres.reverse) :: rest
    }

    res.head
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
    traverse(e, ()) { (e, env, op) =>
      f(e)
      op.sup(e, env)
    }
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
    traverse(e, ()) { (e, env, op) =>
      op.sup(e, env)
      f(e)
    }
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
  def preMap(f: Source => Option[Source], applyRec: Boolean = false)(e: Source): Target = {
    transform(e, ()) { (e, env, op) =>
      op.sup(if (applyRec) fixpoint[Source](e => f(e).getOrElse(e))(e) else f(e).getOrElse(e), env)
    }
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
  def postMap(f: Target => Option[Target], applyRec: Boolean = false)(e: Source): Target = {
    transform(e, ()) { (e, env, op) =>
      val re = op.sup(e, env)
      if (applyRec) fixpoint[Target](e => f(e).getOrElse(e))(re) else f(re).getOrElse(re)
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
                          combiner: (Target, Seq[C]) => C)(init: C)(expr: Source): (Target, C) = {

    var stack: List[Int] = Nil
    var res: List[C] = Nil

    val resE = transform(expr, init) { (e, env, op) =>
      val (preE, preEnv) = pre(e, env)

      // Count this node in the stack and setup for recursion
      if (stack.nonEmpty) stack = (stack.head + 1) :: stack.tail
      stack = 0 :: stack

      // Recurse on the node's children
      val recE = op.sup(preE, preEnv)

      // Recover the sub-contexts from the stack
      val (recEnvs, rest) = res.splitAt(stack.head)
      val recEnv = combiner(recE, recEnvs.reverse)

      val (postE, postEnv) = post(recE, recEnv)

      stack = stack.tail
      res = postEnv :: rest
      postE
    }

    (resE, res.head)
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
    transform(e, c) { (e, env, op) =>
      val (re, renv) = if (applyRec) {
        var ctx = env
        val finalV = fixpoint{ (e: Source) =>
          val res = f(e, ctx)
          ctx = res._2
          res._1.getOrElse(e)
        } (e)
        (finalV, ctx)
      } else {
        val res = f(e, env)
        (res._1.getOrElse(e), res._2)
      }

      op.sup(re, renv)
    }
  }

  def preFoldWithContext[C](f: (Source, C) => C, combiner: (Source, C, Seq[C]) => C)
                           (e: Source, c: C): C = {
    var stack: List[Int] = Nil
    var res: List[C] = Nil

    traverse(e, c) { (e, env, op) =>
      if (stack.nonEmpty) stack = (stack.head + 1) :: stack.tail
      stack = 0 :: stack
      val renv = f(e, env)
      op.sup(e, renv)
      val (rres, rest) = res.splitAt(stack.head)
      stack = stack.tail
      res = combiner(e, env, rres.reverse) :: rest
    }

    res.head
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
    var result: Boolean = false
    traverse(e, ()) { (e, env, op) =>
      if (matcher(e)) result = true
      else if (!result) op.sup(e, env)
    }
    result
  }

  /** Collects a set of objects from all sub-expressions */
  def collect[T](matcher: Source => Set[T])(e: Source): Set[T] = {
    val result = scala.collection.mutable.Set.empty[T]
    traverse(e, ()) { (e, env, op) =>
      result ++= matcher(e)
      op.sup(e, env)
    }
    result.toSet
  }

  def collectPreorder[T](matcher: Source => Seq[T])(e: Source): Seq[T] = {
    val result = new scala.collection.mutable.ListBuffer[T]
    traverse(e, ()) { (e, env, op) =>
      result ++= matcher(e)
      op.sup(e, env)
    }
    result.toSeq
  }

  /** Returns a set of all sub-expressions matching the predicate */
  def filter(matcher: Source => Boolean)(e: Source): Set[Source] = {
    collect[Source] { e => Set(e) filter matcher }(e)
  }

  /** Counts how many times the predicate holds in sub-expressions */
  def count(matcher: Source => Int)(e: Source): Int = {
    var result: Int = 0
    traverse(e, ()) { (e, env, op) =>
      result += matcher(e)
      op.sup(e, env)
    }
    result
  }

  /** Replaces bottom-up sub-expressions by looking up for them in a map */
  def replace(substs: Map[Target, Target], expr: Source): Target = {
    postMap(substs.lift)(expr)
  }

  /** Computes the size of a tree */
  def formulaSize(t: Source): Int = count(_ => 1)(t)

  /** Computes the depth of the tree */
  def depth(e: Source): Int = {
    fold[Int]{ (_, sub) => 1 + (0 +: sub).max }(e)
  }

  object Same {
    def unapply(tt: (Source, Target))
               (implicit ev1: Source =:= Target, ev2: Target =:= Source): Option[(Source, Target)] = {

      // start by collecting the children of `tt._1` ...
      var results: Seq[Source] = Nil
      traverse(tt._1, true) { (e, env, op) =>
        if (env) op.sup(e, false) else results :+= e
      }

      // ... and then inject them into `tt._2`
      val res = scala.util.Try(transform(ev2(tt._2), true) { (e, env, op) =>
        if (env) op.sup(e, false) else {
          val res = results.head
          results = results.tail
          ev2(res)
        }
      })

      if (results.isEmpty && res.toOption == Some(ev2(tt._1))) {
        Some(tt)
      } else {
        None
      }
    }
  }

}
