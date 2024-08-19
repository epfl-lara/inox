/* Copyright 2009-2018 EPFL, Lausanne */

package inox.utils

import scala.collection.mutable.Builder
import scala.collection.mutable.ArrayBuffer
import scala.collection.Iterable

class IncrementalSeq[A] extends IncrementalState
                        with Iterable[A]
                        with Builder[A, IncrementalSeq[A]] {

  private var stack: List[ArrayBuffer[A]] = List(new ArrayBuffer())

  override def clear() : Unit = {
    stack = List(new ArrayBuffer())
  }

  override def reset(): Unit = {
    clear()
  }

  override def push(): Unit = {
    stack ::= stack.head.clone
  }

  override def pop(): Unit = {
    stack = stack.tail
  }

  override def iterator = stack.head.toList.iterator
  override def addOne(e: A) = { stack.head += e; this }
  def -=(e: A) = { stack.head -= e; this }

  override def knownSize: Int = stack.head.size

  override def result() = this
}
