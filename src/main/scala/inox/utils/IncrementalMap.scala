/* Copyright 2009-2016 EPFL, Lausanne */

package inox.utils

import scala.collection.mutable.{Map => MMap, Builder}
import scala.collection.generic.Shrinkable
import scala.collection.IterableLike

class IncrementalMap[A, B] private(dflt: Option[B])
  extends IncrementalState
     with Iterable[(A,B)]
     with IterableLike[(A,B), Map[A,B]]
     with Builder[(A,B), IncrementalMap[A, B]]
     with Shrinkable[A]
     with (A => B) {

  def this() = this(None)

  private var stack: List[MMap[A, B]] = List(MMap())

  override def clear(): Unit = {
    stack = List(MMap())
  }

  def reset(): Unit = {
    clear()
  }

  def push(): Unit = {
    val last = MMap[A,B]() ++ stack.head

    val withDefault = dflt match {
      case Some(value) => last.withDefaultValue(value)
      case None => last
    }

    stack ::= withDefault
  }

  def pop(): Unit = {
    stack = stack.tail
  }

  def withDefaultValue[B1 >: B](dflt: B1) = {
    val map = new IncrementalMap[A, B1](Some(dflt))
    map.stack = map.stack.tail
    for (s <- stack) map.stack ::= MMap[A,B1]().withDefaultValue(dflt) ++ s
    map
  }

  def get(k: A) = stack.head.get(k)
  def apply(k: A) = stack.head.apply(k)
  def contains(k: A) = stack.head.contains(k)
  def isDefinedAt(k: A) = stack.head.isDefinedAt(k)
  def getOrElse[B1 >: B](k: A, e: => B1) = stack.head.getOrElse(k, e)
  def values = stack.head.values

  def cached(k: A)(b: => B): B = getOrElse(k, {
    val ev = b
    this += k -> ev
    ev
  })

  def iterator = stack.head.iterator
  def +=(kv: (A, B)) = { stack.head += kv; this }
  def -=(k: A) = { stack.head -= k; this }

  override def seq = stack.head.seq
  override def newBuilder = new scala.collection.mutable.MapBuilder(Map.empty[A,B])
  def result = this
}
