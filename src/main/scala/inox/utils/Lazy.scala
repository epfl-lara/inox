/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

/** Class that provides deadlock-free lazyness */
class Lazy[T](computeValue: => T) {
  @volatile private var computed: Boolean = false
  private var value: T = scala.compiletime.uninitialized

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
