/* Copyright 2017 EPFL, Lausanne */

package inox
package parsing

import scala.util.parsing.input._

case class ErrorLocation(error: String, pos: Position) {
  override def toString: String = error + "\n" + pos.longString
}