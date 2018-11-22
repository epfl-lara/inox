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

  test("Multiple lets.") {
    val e = e"""
      let x = let z = 3; z + z;
      let y = x;

      x + y
    """

    e match {
      case Let(x, Let(z, IntegerLiteral(_), Plus(z1, z2)), Let(y, x1, Plus(x2, y1))) => {
        assert(x.id.name == "x")
        assert(y.id.name == "y")
        assert(z.id.name == "z")
        assert(x.toVariable == x1)
        assert(x.toVariable == x2)
        assert(y.toVariable == y1)
        assert(z.toVariable == z1)
        assert(z.toVariable == z2)
      }
      case _ => fail("Did not match.")
    }
  }
}