/* Copyright 2009-2016 EPFL, Lausanne */

package inox.utils

import scala.collection.mutable.Builder
import scala.collection.mutable.ArrayBuffer
import scala.collection.{Iterable, IterableLike}

class IncrementalSeq[A] extends IncrementalState
                        with Iterable[A]
                        with IterableLike[A, Seq[A]]
                        with Builder[A, IncrementalSeq[A]] {

  private[this] var stack: List[ArrayBuffer[A]] = List(new ArrayBuffer())

  def clear() : Unit = {
    stack = List(new ArrayBuffer())
  }

  def reset(): Unit = {
    clear()
  }

  def push(): Unit = {
    stack ::= stack.head.clone
  }

  def pop(): Unit = {
    stack = stack.tail
  }

  def iterator = stack.head.toList.iterator
  def +=(e: A) = { stack.head += e; this }
  def -=(e: A) = { stack.head -= e; this }

  override def newBuilder = new scala.collection.mutable.ArrayBuffer()
  def result = this
}
