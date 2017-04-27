/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

trait Extractor {
  type Match = Map[Int, Any]

  def matching(index: Int, value: Any): Match = Map(index -> value)
  val empty: Match = Map()
  val success = Some(Map[Int, Any]())
  val fail = None
}