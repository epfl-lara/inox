package inox
package parser

import org.scalatest._

class ProgramsParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing program with one ADT, one function.") {
    val Seq(listSort, sizeFunDef) = p"""
      type List[A] = Cons(head: A, tail: List[A]) | Nil()

      def size[A](xs: List[A]): Integer =
        if (xs is Cons) 1 + size(xs.tail) else 0
    """

    assert(listSort.id.name == "List")
    assert(sizeFunDef.id.name == "size")
  }

  test("Parsing program with zero ADT, three mutually recursive functions.") {
    val Seq(fooFunDef, barFunDef, bazFunDef) = p"""

      def foo(x: Int, y: Int) = bar(x) + baz(y)

      def bar(x: Int) = if (x > 0) foo(x - 1, x - 1) * bar(x - 1) else bar(1)

      def baz(y: Int): Int = 4 + bar(y) * foo(1, 1)
    """

    assert(fooFunDef.id.name == "foo")
    assert(barFunDef.id.name == "bar")
    assert(bazFunDef.id.name == "baz")
  }

  test("Parsing program with three mutually dependent ADTs.") {
    val Seq(fooSort, barSort, bazSort) = p"""
      type Foo[A, B] = FooBar(getBar: Bar[A]) | FooBaz(getBaz: Baz[B])

      type Bar[A] = BarFoo(getFoo: Foo[A, A]) | BarBar(getBar: Bar[A])

      type Baz[X] = BazBarFoo(getBar: Bar[X], getFoo: Foo[Integer, Integer])
    """

    assert(fooSort.id.name == "Foo")
    assert(barSort.id.name == "Bar")
    assert(bazSort.id.name == "Baz")
  }

  test("Order of definitions is preserved.") {
    val Seq(fooSort, barFunDef, bazSort, fooBazFunDef) = p"""
      type Foo[A] = Foo(getFoo: A)

      def bar[A](x: Foo[A]): A = x.getFoo

      type Baz[A] = Baz(getBaz: Foo[A])

      def fooBaz[A, B](foo: Foo[A], baz: Baz[B]) = 4
    """

    assert(fooSort.id.name == "Foo")
    assert(barFunDef.id.name == "bar")
    assert(bazSort.id.name == "Baz")
    assert(fooBazFunDef.id.name == "fooBaz")

    assert(fooSort.isInstanceOf[ADTSort])
    assert(barFunDef.isInstanceOf[FunDef])
    assert(bazSort.isInstanceOf[ADTSort])
    assert(fooBazFunDef.isInstanceOf[FunDef])
  }
}