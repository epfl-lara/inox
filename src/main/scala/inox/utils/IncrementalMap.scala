/* Copyright 2009-2018 EPFL, Lausanne */

package inox.utils

import scala.collection.mutable.{Map => MMap, Builder, Shrinkable}

class IncrementalMap[A, B] private(dflt: Option[B])
  extends IncrementalState
     with Iterable[(A,B)]
     with Builder[(A,B), IncrementalMap[A, B]]
     with Shrinkable[A]
     with (A => B) {

  def this() = this(None)

  private def withDefault(map: MMap[A, B]): MMap[A, B] = dflt match {
    case Some(value) => map.withDefaultValue(value)
    case None => map
  }

  private var stack: List[MMap[A, B]] = List(withDefault(MMap()))

  override def clear(): Unit = {
    stack = List(withDefault(MMap()))
  }

  override def reset(): Unit = {
    clear()
  }

  override def push(): Unit = {
    stack ::= withDefault(MMap[A, B]() ++ stack.head)
  }

  override def pop(): Unit = {
    stack = stack.tail
  }

  def withDefaultValue[B1 >: B](dflt: B1) = {
    val map = new IncrementalMap[A, B1](Some(dflt))
    map.stack = stack.map(frame => map.withDefault(MMap[A, B1]() ++ frame))
    map
  }

  def get(k: A) = stack.head.get(k)
  override def apply(k: A) = stack.head.apply(k)
  def contains(k: A) = stack.head.contains(k)
  def isDefinedAt(k: A) = stack.head.isDefinedAt(k)
  def getOrElse[B1 >: B](k: A, e: => B1) = stack.head.getOrElse(k, e)
  def values = stack.head.values

  def cached(k: A)(b: => B): B = getOrElse(k, {
    val ev = b
    this += k -> ev
    ev
  })

  override def iterator = stack.head.iterator
  override def addOne(kv: (A, B)) = { stack.head += kv; this }
  override def subtractOne(k: A) = { stack.head -= k; this }

  override def knownSize: Int = stack.head.size

  override def result() = this
}
