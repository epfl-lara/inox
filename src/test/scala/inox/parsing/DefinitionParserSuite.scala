/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package parsing

import org.scalatest.funsuite.AnyFunSuite

/** Parsing of sorts and functions with the `td"..."` and `fd"..."` interpolators, and of
  * expressions that use them.
  */
class DefinitionParserSuite extends AnyFunSuite {

  import inox.trees.{given, _}
  import interpolator.{given, _}

  val listSort: ADTSort = {
    given Symbols = NoSymbols
    td"type List[A] = Cons(head: A, tail: List[A]) | Nil()"
  }

  val optionSort: ADTSort = {
    given Symbols = NoSymbols
    td"type Opt[T] = Some(value: T) | None"
  }

  val List(consCons, nilCons) = listSort.constructors.toList: @unchecked
  val List(someCons, noneCons) = optionSort.constructors.toList: @unchecked

  val sortSymbols = NoSymbols.withSorts(Seq(listSort, optionSort))

  val sizeFd: FunDef = {
    given Symbols = sortSymbols
    fd"def size[A](l: List[A]): BigInt = if (l is Cons) 1 + size[A](l.tail) else 0"
  }

  val headOptionFd: FunDef = {
    given Symbols = sortSymbols
    fd"def headOption[A](l: List[A]): Opt[A] = if (l is Cons) Some[A](l.head) else None[A]()"
  }

  val constFd: FunDef = {
    given Symbols = sortSymbols
    fd"def const: BigInt = 42"
  }

  given symbols: Symbols = sortSymbols.withFunctions(Seq(sizeFd, headOptionFd, constFd))

  test("Parsing sorts") {
    assert(listSort.id.name == "List")
    assert(listSort.tparams.size == 1)
    assert(consCons.id.name == "Cons" && nilCons.id.name == "Nil")
    val List(head, tail) = consCons.fields.toList: @unchecked
    assert(head.id.name == "head" && head.tpe == listSort.tparams.head.tp)
    assert(tail.id.name == "tail" && tail.tpe == ADTType(listSort.id, Seq(listSort.tparams.head.tp)))
    assert(nilCons.fields.isEmpty)
    assert(noneCons.fields.isEmpty)
    assert(symbols.ensureWellFormed == ())
  }

  test("Parsing functions") {
    assert(sizeFd.id.name == "size")
    assert(sizeFd.tparams.size == 1)
    assert(sizeFd.params.map(_.id.name) == Seq("l"))
    assert(sizeFd.returnType == IntegerType())
    sizeFd.fullBody match {
      case IfExpr(IsConstructor(l, cons), Plus(IntegerLiteral(one), FunctionInvocation(size, Seq(tp), Seq(ADTSelector(l2, tail)))), IntegerLiteral(zero)) =>
        assert(l == sizeFd.params.head.toVariable && l2 == l)
        assert(cons == consCons.id && size == sizeFd.id && tail == consCons.fields(1).id)
        assert(tp == sizeFd.tparams.head.tp)
        assert(one == 1 && zero == 0)
      case body => fail(s"Unexpected body $body")
    }
    assert(constFd.params.isEmpty && constFd.fullBody == IntegerLiteral(42))
    assert(headOptionFd.returnType == ADTType(optionSort.id, Seq(headOptionFd.tparams.head.tp)))
  }

  test("Parsing expressions over ADTs") {
    e"Cons[BigInt](1, Nil[BigInt]())" match {
      case ADT(cons, Seq(IntegerType()), Seq(IntegerLiteral(one), ADT(nil, Seq(IntegerType()), Seq()))) =>
        assert(cons == consCons.id && nil == nilCons.id && one == 1)
      case e => fail(s"Unexpected $e")
    }

    // type arguments are inferred
    assert(e"Cons(1 : Int, Nil())".getType == ADTType(listSort.id, Seq(Int32Type())))

    e"lambda l: List[BigInt]. l.head" match {
      case Lambda(Seq(l), ADTSelector(vl, head)) =>
        assert(vl == l.toVariable && head == consCons.fields.head.id)
      case e => fail(s"Unexpected $e")
    }

    e"lambda l: List[BigInt]. l is Nil" match {
      case Lambda(Seq(l), IsConstructor(vl, nil)) =>
        assert(vl == l.toVariable && nil == nilCons.id)
      case e => fail(s"Unexpected $e")
    }

    e"Some(true)" match {
      case ADT(some, Seq(BooleanType()), Seq(BooleanLiteral(true))) => assert(some == someCons.id)
      case e => fail(s"Unexpected $e")
    }
  }

  test("Parsing function calls") {
    e"size[BigInt](Nil[BigInt]())" match {
      case FunctionInvocation(size, Seq(IntegerType()), Seq(ADT(nil, _, _))) =>
        assert(size == sizeFd.id && nil == nilCons.id)
      case e => fail(s"Unexpected $e")
    }

    e"size(Cons(true, Nil()))" match {
      case FunctionInvocation(size, Seq(BooleanType()), Seq(_)) => assert(size == sizeFd.id)
      case e => fail(s"Unexpected $e")
    }

    assert(e"headOption(Cons('a', Nil()))".getType == ADTType(optionSort.id, Seq(StringType())))
    assert(e"const() + 1" == Plus(FunctionInvocation(constFd.id, Seq(), Seq()), IntegerLiteral(1)))
  }

  test("Parsing types of sorts") {
    assert(t"List[Int]" == ADTType(listSort.id, Seq(Int32Type())))
    assert(t"Opt[List[Boolean]]" == ADTType(optionSort.id, Seq(ADTType(listSort.id, Seq(BooleanType())))))
  }

  test("Extracting sorts and functions") {
    listSort match {
      case td"type List[A] = Cons(head: A, tail: List[A]) | Nil()" => succeed
      case _ => fail("Did not match.")
    }

    listSort match {
      case td"type Opt[A] = Some(value: A) | None()" => fail("Did match.")
      case _ => succeed
    }

    sizeFd match {
      case fd"def size[A](l: List[A]): BigInt = if (l is Cons) 1 + size[A](l.tail) else $e" =>
        assert(e == IntegerLiteral(0))
      case _ => fail("Did not match.")
    }

    sizeFd match {
      case fd"def size[A](l: List[A]): $t = $body" =>
        assert(t == IntegerType())
        assert(body == sizeFd.fullBody)
      case _ => fail("Did not match.")
    }

    constFd match {
      case fd"def const: BigInt = 43" => fail("Did match.")
      case fd"def const: BigInt = $e" => assert(e == IntegerLiteral(42))
      case _ => fail("Did not match.")
    }
  }

  test("Extracting expressions over ADTs") {
    val l = Variable.fresh("l", ADTType(listSort.id, Seq(IntegerType())))
    val call = FunctionInvocation(sizeFd.id, Seq(IntegerType()), Seq(l))

    call match {
      case e"size($x)" => assert(x == l)
      case _ => fail("Did not match.")
    }

    ADTSelector(l, consCons.fields.head.id) match {
      case e"$x.head" => assert(x == l)
      case _ => fail("Did not match.")
    }

    IsConstructor(l, consCons.id) match {
      case e"$x is Nil" => fail("Did match.")
      case e"$x is Cons" => assert(x == l)
      case _ => fail("Did not match.")
    }

    ADT(consCons.id, Seq(IntegerType()), Seq(IntegerLiteral(1), l)) match {
      case e"Cons($h, $t)" =>
        assert(h == IntegerLiteral(1) && t == l)
      case _ => fail("Did not match.")
    }
  }

  test("Definition parsing errors") {
    given Symbols = NoSymbols
    intercept[Exception](td"type = A")
    intercept[Exception](td"type T = ")
    intercept[Exception](fd"def f(x: BigInt) = x")
    intercept[Exception](fd"def f(x: BigInt): Boolean = x")
    intercept[Exception](fd"def f(x: Unknown): BigInt = 1")
  }
}
