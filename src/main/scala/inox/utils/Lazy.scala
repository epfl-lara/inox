/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

/** Class that provides deadlock-free lazyness */
class Lazy1[S, T](computeValue: S => T) {
  @volatile
  private[this] var computed: Map[S, T] = Map.empty

  def get(s: S): T = {
    if (!computed.contains(s)) {
      computed = computed.updated(s, computeValue(s))
    }
    computed(s)
  }
}

object Lazy1 {
  def apply[T, S](f: T => S): Lazy1[T, S] = new Lazy1(f)
}

class Lazy[T](computeValue: => T) {
  @volatile
  private[this] var computed: Boolean = false

  private[this] var value: T = _

  def get: T = {
    if (!computed) {
      value = computeValue
      computed = true
    }
    value
  }
}

object Lazy {
  def apply[T](b: => T): Lazy[T] = new Lazy(b)
}

