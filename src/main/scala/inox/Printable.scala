/* Copyright 2009-2016 EPFL, Lausanne */

package inox

/** A trait for objects that can be pretty-printed given a [[inox.Context]] */
trait Printable {
  def asString(implicit ctx: Context): String
}
