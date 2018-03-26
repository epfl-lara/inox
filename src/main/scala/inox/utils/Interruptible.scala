/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

trait Interruptible {
  def interrupt(): Unit
}
