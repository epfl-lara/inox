/* Copyright 2009-2017 EPFL, Lausanne */

package inox
package utils

/** Class that provides deadlock-free lazyness */
class Lazy[T](computeValue: => T) {
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
