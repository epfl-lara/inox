package inox
package parser

import scala.util.parsing.input._

object Errors {

  def withPosition(error: String): Position => String =
    (pos: Position) => error + "\n" + pos.longString

  /* Parsing errors: */

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

  /* Elaboration errors: */

  def invalidHoleType(tpe: String): Position => String =
    withPosition("Invalid argument passed to hole. Expected a value of type " + tpe + ".")

  def invalidInoxType(tpe: inox.ast.Trees#Type): Position => String =
    withPosition("Invalid Type " + tpe + ".")

  def noTypeInScope(name: String): Position => String =
    withPosition("No type named " + name + " is available in scope.")

  def noExprInScope(name: String): Position => String =
    withPosition("No expression named " + name + " is available in scope.")

  def sortUsedAsTypeVariable(name: String): Position => String =
    withPosition(name + " is a sort, not a type variable.")

  def typeVariableUsedAsSort(name: String): Position => String =
    withPosition(name + " is a type variable, not a sort.")

  def wrongNumberOfArguments(callee: String, expected: Int, actual: Int): Position => String =
    withPosition("Wrong number of arguments for " + callee + ", expected " + expected + ", got " + actual + ".")

  def wrongNumberOfTypeArguments(callee: String, expected: Int, actual: Int): Position => String =
    withPosition("Wrong number of type arguments for " + callee + ", expected " + expected + ", got " + actual + ".")
}