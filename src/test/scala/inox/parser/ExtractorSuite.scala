package inox
package parser

import org.scalatest._

class ExtractorSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Extracting entire expression") {
    val es = Seq(
      e"true",
      e"12 + 3",
      e"forall (x) => x + x > 12.0",
      e"choose (x) => x * x == 2.0")

    for (e <- es) {
      e match {
        case e"$x" => assert(e == x)
        case _ => fail("Did not match.")
      }

      e match {
        case e"  $x   " => assert(e == x)
        case _ => fail("Did not match.")
      }
    }
  }

  test("Matching arithmetic operation") {

    e"3 + 4" match {
      case e"4 + $x" => fail("Did match.")
      case e"3 + 2" => fail("Did match.")
      case e"$x + 4" => assert(x == IntegerLiteral(3))
      case _ => fail("Did not match.")
    }

    e"3 * 4 + 5" match {
      case e"3 * (4 + 5)" => fail("Did match.")
      case e"3 * 5 + 4" => fail("Did match.")
      case e"$x * $y + $z" => {
        assert(x == IntegerLiteral(3))
        assert(y == IntegerLiteral(4))
        assert(z == IntegerLiteral(5))
      }
      case _ => fail("Did not match.")
    }

    e"2 + 4 - 3 / 5 * 2" match {
      case e"$x * $y" => fail("Did match.")
      case e"$x as Real - (3 / $y) * $z" => fail("Did match.")
      case e"$x - (3 as Integer / $y) * $z" => {
        assert(x == Plus(IntegerLiteral(2), IntegerLiteral(4)))
        assert(y == IntegerLiteral(5))
        assert(z == IntegerLiteral(2))
      }
      case _ => fail("Did not match.")
    }
  }

  test("Matching against polymorphic values.") {
    val es = Seq(IntegerLiteral(1), Int32Literal(1), FractionLiteral(1, 1), BVLiteral(true, 1, 12))

    for (e <- es) {
      e match {
        case e"1" => succeed
        case _ => fail("Did not match.")
      }
    }
  }

  test("Matching dependent types.") {
    t"{ x: Integer | x > 0 }" match {
      case t"{ $v: $t | $e }" =>
        assert(t == IntegerType())
        e match {
          case GreaterThan(Variable(id, IntegerType(), _), IntegerLiteral(i)) =>
            assert(id.name == "x")
            assert(i == 0)
          case _ => fail("Invalid extraction.")
        }
      case _ => fail("Did not match.")
    }

    t"{ y: Unit | true }" match {
      case t"{ $t | false }" => fail("Did match.")
      case t"{ x: $t | $p }" =>
        assert(t == UnitType())
        assert(p == BooleanLiteral(true))
      case _ => fail("Did not match.")
    }

    t"Pi (x: Int) => { y: Int | x < y }" match {
      case t"Int => Int" => fail("Did match.")
      case t"Int => $t" => fail("Did match.")
      case t"Pi (x: $t) => $t2" =>
        assert(t == Int32Type())
      case _ => fail("Did not match.")
    }
  }

  test("Matching primitive invocations.") {
    e"concatenate('hello', 'world')" match {
      case e"$x('hello', 'world')" => fail("Did match.")
      case e"concatenate('hello', 'world')" => ()
    }
  }
}
