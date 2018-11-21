package inox
package parser

import org.scalatest._

class LetParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing let expression with explicitly typed binding.") {
    val e = e"let x: String = 'Hello World'; length(x)"

    assert(e.isInstanceOf[Let])

    val l = e.asInstanceOf[Let]

    assert(l.vd.id.name == "x")
    assert(l.vd.tpe == StringType())
    assert(l.value == StringLiteral("Hello World"))
    assert(l.body == StringLength(l.vd.toVariable))
  }

  test("Parsing let expression with implicitly typed binding.") {
    val e = e"let x = 'Hello World'; length(x)"

    assert(e.isInstanceOf[Let])

    val l = e.asInstanceOf[Let]

    assert(l.vd.id.name == "x")
    assert(l.vd.tpe == StringType())
    assert(l.value == StringLiteral("Hello World"))
    assert(l.body == StringLength(l.vd.toVariable))
  }
}