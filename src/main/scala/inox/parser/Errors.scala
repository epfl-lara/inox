package inox
package parser

import scala.util.parsing.input._

object Errors {

  def expected(string: String): Position => String =
    withPosition("Expected " + string + ".")

  def expectedString(string: String): Position => String =
    expected("\"" + string + "\"")

  def expectedOneOf(strings: String*): Position => String = {
    assert(strings.size >= 1)

    if (strings.size == 1) {
      expectedString(strings.head)
    }
    else {
      withPosition("Expected either " + strings.init.mkString(", ") + " or " + strings.last + ".")
    }
  }

  def expectedOneOfStrings(strings: String*): Position => String =
    expectedOneOf(strings.map(x => "\"" + x + "\""): _*)

  def withPosition(error: String): Position => String =
    (pos: Position) => error + "\n" + pos.longString
}