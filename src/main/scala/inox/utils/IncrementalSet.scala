/* Copyright 2009-2018 EPFL, Lausanne */

package inox.utils

import scala.collection.mutable.{Set => MSet, Builder}
import scala.collection.Iterable

/** A stack of mutable sets with a set-like API and methods to push and pop */
class IncrementalSet[A] extends IncrementalState
                        with Iterable[A]
                        with Builder[A, IncrementalSet[A]] {

  private var stack = List[MSet[A]](MSet())

  /** Removes all the elements */
  override def clear(): Unit = {
    stack = List(MSet())
  }

  /** Removes all the elements and creates a new set */
  override def reset(): Unit = {
    clear()
  }

  /** Creates one more set level */
  override def push(): Unit = {
    stack ::= stack.head.clone
  }

  /** Removes one set level */
  override def pop(): Unit = {
    stack = stack.tail
  }

  /** Returns true if the set contains elem */
  def apply(elem: A) = stack.head.contains(elem)
  /** Returns true if the set contains elem */
  def contains(elem: A) = stack.head.contains(elem)

  /** Returns an iterator over all the elements */
  override def iterator = stack.head.iterator
  /** Add an element to the head set */
  override def addOne(elem: A) = { stack.head += elem; this }
  /** Removes an element from all stacked sets */
  def -= (elem: A) = { stack.head -= elem; this }

  override def knownSize: Int = stack.head.size

  override def result() = this
}
