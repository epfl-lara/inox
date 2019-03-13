package inox
package parser

import org.scalatest._

class ExprParserSuite extends FunSuite {

  import inox.trees._
  import interpolator._
  implicit val symbols = NoSymbols

  test("Parsing expressions with various parentheses.") {

    assert(e"((1))" == IntegerLiteral(1))

    assert(e"({ 2} + (3))" == Plus(IntegerLiteral(2), IntegerLiteral(3)))

    assert(e"{ let x = 4; x + x }".isInstanceOf[Let])
  }

  test("Parsing lambda expressions.") {
    val e1 = e"lambda (x: Int) => x"

    assert(e1.isInstanceOf[Lambda])

    val l1 = e1.asInstanceOf[Lambda]

    assert(l1.params.size == 1)

    assert(l1.params(0).id.name == "x")
    assert(l1.params(0).tpe == Int32Type())
    assert(l1.body == l1.params(0).toVariable)

    val e2 = e"lambda (x) => x + 1"

    assert(e2.isInstanceOf[Lambda])

    val l2 = e2.asInstanceOf[Lambda]

    assert(l2.params.size == 1)

    assert(l2.params(0).id.name == "x")
    assert(l2.params(0).tpe == IntegerType())
    assert(l2.body == Plus(l2.params(0).toVariable, IntegerLiteral(1)))

    assert(e"(foo: Integer) => foo * foo".isInstanceOf[Lambda])

    val e3 = e"(foo: String, bar) => length(foo) + bar"

    assert(e3.isInstanceOf[Lambda])

    val l3 = e3.asInstanceOf[Lambda]

    assert(l3.params.size == 2)

    assert(l3.params(0).id.name == "foo")
    assert(l3.params(1).id.name == "bar")
    assert(l3.params(0).tpe == StringType())
    assert(l3.params(1).tpe == IntegerType())
    assert(l3.body == Plus(StringLength(l3.params(0).toVariable), l3.params(1).toVariable))
  }

  test("Parsing forall expressions.") {
    val e1 = e"forall (x: Int) => x > 0"

    assert(e1.isInstanceOf[Forall])

    val l1 = e1.asInstanceOf[Forall]

    assert(l1.params.size == 1)

    assert(l1.params(0).id.name == "x")
    assert(l1.params(0).tpe == Int32Type())
    assert(l1.body == GreaterThan(l1.params(0).toVariable, Int32Literal(0)))

    val e2 = e"forall (x) => x == 1"

    assert(e2.isInstanceOf[Forall])

    val l2 = e2.asInstanceOf[Forall]

    assert(l2.params.size == 1)

    assert(l2.params(0).id.name == "x")
    assert(l2.params(0).tpe == IntegerType())
    assert(l2.body == Equals(l2.params(0).toVariable, IntegerLiteral(1)))

    val e3 = e"forall (foo: String, bar) => length(foo) == bar"

    assert(e3.isInstanceOf[Forall])

    val l3 = e3.asInstanceOf[Forall]

    assert(l3.params.size == 2)

    assert(l3.params(0).id.name == "foo")
    assert(l3.params(1).id.name == "bar")
    assert(l3.params(0).tpe == StringType())
    assert(l3.params(1).tpe == IntegerType())
    assert(l3.body == Equals(StringLength(l3.params(0).toVariable), l3.params(1).toVariable))
  }

  test("Parsing choose expressions.") {
    val e1 = e"choose (x: Int) => x > 0"

    assert(e1.isInstanceOf[Choose])

    val l1 = e1.asInstanceOf[Choose]

    assert(l1.res.id.name == "x")
    assert(l1.res.tpe == Int32Type())
    assert(l1.pred == GreaterThan(l1.res.toVariable, Int32Literal(0)))

    val e2 = e"choose (x) => x == 1"

    assert(e2.isInstanceOf[Choose])

    val l2 = e2.asInstanceOf[Choose]

    assert(l2.res.id.name == "x")
    assert(l2.res.tpe == IntegerType())
    assert(l2.pred == Equals(l2.res.toVariable, IntegerLiteral(1)))
  }

  test("Parsing if-expressions.") {
    val e = e"if (3 > 4) 'Hello.' else 'Hi!'"

    assert(e.isInstanceOf[IfExpr])

    val i = e.asInstanceOf[IfExpr]

    assert(i.cond == GreaterThan(IntegerLiteral(3), IntegerLiteral(4)))
    assert(i.thenn == StringLiteral("Hello."))
    assert(i.elze == StringLiteral("Hi!"))
  }

  test("Parsing assume.") {
    val e = e"assume(3 > 4); 7"

    assert(e.isInstanceOf[Assume])

    val a = e.asInstanceOf[Assume]

    assert(a.pred == GreaterThan(IntegerLiteral(3), IntegerLiteral(4)))
    assert(a.body == IntegerLiteral(7))
  }
}