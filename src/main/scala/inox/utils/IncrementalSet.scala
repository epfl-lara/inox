/* Copyright 2009-2016 EPFL, Lausanne */

package inox.utils

import scala.collection.mutable.{Stack, Set => MSet}
import scala.collection.mutable.Builder
import scala.collection.{Iterable, IterableLike, GenSet}

/** A stack of mutable sets with a set-like API and methods to push and pop */
class IncrementalSet[A] extends IncrementalState
                        with Iterable[A]
                        with IterableLike[A, Set[A]]
                        with Builder[A, IncrementalSet[A]] {

  private[this] var stack = List[MSet[A]](MSet())
  override def repr = stack.head.toSet

  /** Removes all the elements */
  override def clear(): Unit = {
    stack = List(MSet())
  }

  /** Removes all the elements and creates a new set */
  def reset(): Unit = {
    clear()
  }

  /** Creates one more set level */
  def push(): Unit = {
    stack ::= stack.head.clone
  }

  /** Removes one set level */
  def pop(): Unit = {
    stack = stack.tail
  }

  /** Returns true if the set contains elem */
  def apply(elem: A) = stack.head.contains(elem)
  /** Returns true if the set contains elem */
  def contains(elem: A) = stack.head.contains(elem)

  /** Returns an iterator over all the elements */
  def iterator = stack.head.iterator
  /** Add an element to the head set */
  def += (elem: A) = { stack.head += elem; this }
  /** Removes an element from all stacked sets */
  def -= (elem: A) = { stack.head -= elem; this }

  override def newBuilder = new scala.collection.mutable.SetBuilder(Set.empty[A])
  def result = this
}
