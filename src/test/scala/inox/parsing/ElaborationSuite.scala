/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package parsing

import org.scalatest.funsuite.AnyFunSuite

class ElaborationSuite extends AnyFunSuite {

  import inox.trees.{given, _}
  import interpolator.{given, _}

  val listSort: ADTSort = {
    given Symbols = NoSymbols
    td"type List[A] = Cons(head: A, tail: List[A]) | Nil()"
  }
  val List(consCons, nilCons) = listSort.constructors.toList: @unchecked

  val sizeFd: FunDef = {
    given Symbols = NoSymbols.withSorts(Seq(listSort))
    fd"def size[A](l: List[A]): BigInt = if (l is Cons) 1 + size[A](l.tail) else 0"
  }

  given symbols: Symbols = NoSymbols.withSorts(Seq(listSort)).withFunctions(Seq(sizeFd))

  def succeeds(body: => Any): Unit = body

  def failsWith(msg: String)(body: => Any): Unit = {
    val ex = intercept[Exception](body)
    assert(ex.getMessage.contains(msg), s"for message ${ex.getMessage}")
  }

  test("elaboration of expressions and types, and its errors") {
    val x = Variable.fresh("x", IntegerType())
    val l = Variable.fresh("l", ADTType(listSort.id, Seq(IntegerType())))
    succeeds(e"+ $x")
    succeeds(e"$x != 2")
    failsWith("Primitive function `length` takes 1 argument, 2 were given.")(e"length('a', 'b')")
    failsWith("Primitive function `length` doesn't have any type parameters.")(e"length[Int]('a')")
    failsWith("Not all elements are of the same shape. Use bindings of the form `key -> value` for bag literals and naked values for set literals.")(e"{1, 2 -> 3}")
    failsWith("Not all elements are of the same shape. Use bindings of the form `key -> value` for bag literals and naked values for set literals.")(e"{1 -> 2, 3}")
    failsWith("Expected binding of the form `key -> value`.")(e"Bag[BigInt](1)")
    succeeds(e"Map[BigInt, BigInt](1)")
    failsWith("Expected binding of the form `key -> value`.")(e"{* -> 1, 2}")
    failsWith("Unexpected binding. Bindings can only appear in bags and maps constructors.")(e"1 -> 2")
    failsWith("Function `size` takes 1 argument, 0 were given.")(e"size[BigInt]()")
    failsWith("Function `size` takes 1 type argument, 2 were given.")(e"size[BigInt, BigInt](Nil[BigInt]())")
    assert(e"Cons(1, Nil())".getType == ADTType(listSort.id, Seq(IntegerType())))
    succeeds(e"$l is Cons")
    succeeds(e"$l.head")
    failsWith("Unexpected construct.")(e"$l.foo")
    failsWith("Expression expected.")(e"${1.5} + 1")
    failsWith("Unknown variable x.")(e"${x.id} + 1")
    succeeds(e"size(${Seq[Expr](l)}...)")
    failsWith("Missing `)`.")(e"(${Seq[Expr](x, x)}...)")
    failsWith("Type constructor Set takes 1 argument, 2 were given.")(t"Set[Int, Int]")
    failsWith("Unknown type constructor: Foo")(t"Foo[Int]")
    failsWith("Type List expects 1 argument, none were given")(t"List")
    succeeds(t"List[BigInt]")
    failsWith("Type constructor List takes 1 argument, 2 were given.")(t"List[BigInt, BigInt]")
    assert(t"(x: BigInt, {y: BigInt | y > x})".isInstanceOf[SigmaType])
    assert(t"(x: BigInt) => {y: BigInt | y > x}".isInstanceOf[PiType])
    succeeds(t"(x: BigInt, y: BigInt) => {z: BigInt | z > x + y}")
    assert(t"{x: BigInt | x > 0}".isInstanceOf[RefinementType])
    succeeds(t"{BigInt | true}")
    succeeds(t"(x: BigInt, BigInt)")
    failsWith("Type expected.")(t"BigInt => (x: BigInt)")
    assert(t"(${Seq[Type](IntegerType(), BooleanType())}...)" == TupleType(Seq(IntegerType(), BooleanType())))
    succeeds(t"(${Seq[Type](IntegerType(), BooleanType())}...) => BigInt")
    succeeds(t"${listSort.id}[BigInt]")
    failsWith("Ambiguity. Try using type annotations.")(e"lambda y. y")
    failsWith("Occur check.")(e"lambda f. f(f)")
    failsWith("Type BigInt is not a tuple.")(e"$x._1")
    failsWith("is not a tuple.")(e"lambda y. y._1 + size(y)")
    failsWith("Types incompatible: BigInt, List[")(e"lambda y: BigInt. y.head")
    failsWith("Types incompatible: BigInt, List[")(e"$x.head")
    failsWith("Identifier expected.")(e"lambda (y: BigInt, z: BigInt). y + z")
    failsWith("Missing assignment to variable `x`. Use `=` to assign a value to the variable.")(e"let x 1 in x")
    failsWith("Binding expected. Bindings take the form `variable = expression`, and are separated by `,`.")(e"let 1")
    failsWith("Missing condition, between parentheses '(' and ')'.")(e"if true 1 else 2")
    failsWith("Missing `)`.")(e"(1 + 2")
    failsWith("Missing `}`.")(e"{1, 2")
    succeeds(e"{1 -> 2}")
    failsWith("Missing ']'.")(e"size[BigInt(Nil[BigInt]())")
    failsWith("Missing `.` between bindings and expression body.")(e"lambda x 1")
    failsWith("Missing ')' at the end of the arguments.")(e"size(Nil()")
    failsWith("Selector expected.")(e"$l.")
    failsWith("Unexpected construct.")(e"$l.head[BigInt]")
    failsWith("Identifier expected.")(e"lambda (f: BigInt => BigInt => BigInt). f(1)(2)")
    succeeds(v"${x.id}: BigInt")
    assert(e"lambda y. y & 1".getType == FunctionType(Seq(Int32Type()), Int32Type()))
    succeeds(e"lambda y. y | y")
    succeeds(e"lambda y. y % 2")
    assert(e"lambda y. y * 2.5".getType == FunctionType(Seq(RealType()), RealType()))
    failsWith("Type String is not comparable")(e"lambda y. y < 'a'")
    succeeds(e"(1 : Int8) + 1")
    succeeds(e"lambda y. y.head + 1")
    succeeds(e"{1, 2} == {} ")
    failsWith("Identifier expected.")(e"lambda (m: Map[BigInt, BigInt]). m(1)")
    failsWith("Unexpected construct.")(e"'abc'.length")
    failsWith("Types incompatible: BigInt, List[")(e"$x is Cons")
    failsWith("Unknown variable tuple.")(e"tuple(1)")
  }
}
