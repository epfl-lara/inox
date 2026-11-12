/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package parsing

import org.scalatest.funsuite.AnyFunSuite

/** Parsing of the primitive types and operations of the `e"..."` interpolator (strings, sets, bags,
  * maps, tuples, bit-vectors), and of its binders.
  */
class PrimitivesParserSuite extends AnyFunSuite {

  import inox.trees.{given, _}
  import interpolator.{given, _}
  given Symbols = NoSymbols

  private def int(i: Int) = IntegerLiteral(i)

  test("Parsing strings") {
    assertResult(StringConcat(StringLiteral("a"), StringLiteral("b"))) {
      e"'a' ++ 'b'"
    }
    assertResult(StringConcat(StringLiteral("a"), StringLiteral("b"))) {
      e"concatenate('a', 'b')"
    }
    assertResult(StringLength(StringLiteral("abc"))) {
      e"length('abc')"
    }
    assertResult(SubString(StringLiteral("abc"), int(1), int(2))) {
      e"substring('abc', 1, 2)"
    }
    assert(e"length('abc') + 1".getType == IntegerType())
  }

  test("Parsing sets") {
    assertResult(FiniteSet(Seq(int(1), int(2), int(3)), IntegerType())) {
      e"{1, 2, 3}"
    }
    assertResult(FiniteSet(Seq(int(1), int(2)), IntegerType())) {
      e"Set(1, 2)"
    }
    assertResult(FiniteSet(Seq(Int32Literal(1)), Int32Type())) {
      e"Set[Int](1)"
    }
    assertResult(FiniteSet(Seq(), StringType())) {
      e"{} : Set[String]"
    }
    assertResult(FiniteSet(Seq(StringLiteral("foo"), StringLiteral("bar")), StringType())) {
      e"{'foo', 'bar'}"
    }

    val s = FiniteSet(Seq(int(1)), IntegerType())
    val s2 = FiniteSet(Seq(int(2)), IntegerType())
    assertResult(ElementOfSet(int(1), s)) { e"contains({1}, 1)" }
    assertResult(ElementOfSet(int(1), s)) { e"1 ∈ {1}" }
    assertResult(SetAdd(s, int(2))) { e"add({1}, 2)" }
    assertResult(SubsetOf(s, s2)) { e"subset({1}, {2})" }
    assertResult(SubsetOf(s, s2)) { e"{1} ⊆ {2}" }
    assertResult(SetUnion(s, s2)) { e"union({1}, {2})" }
    assertResult(SetUnion(s, s2)) { e"{1} ∪ {2}" }
    assertResult(SetIntersection(s, s2)) { e"intersection({1}, {2})" }
    assertResult(SetIntersection(s, s2)) { e"{1} ∩ {2}" }
    assertResult(SetDifference(s, s2)) { e"difference({1}, {2})" }
    assertResult(SetDifference(s, s2)) { e"{1} ∖ {2}" }

    // element types are inferred from how sets are used
    assert(e"lambda x. contains(x, 1 : Int)".getType == FunctionType(Seq(SetType(Int32Type())), BooleanType()))
  }

  test("Parsing bags") {
    val b = FiniteBag(Seq(int(1) -> int(2), int(3) -> int(4)), IntegerType())
    assertResult(b) { e"{1 -> 2, 3 -> 4}" }
    assertResult(b) { e"Bag(1 -> 2, 3 -> 4)" }
    assertResult(FiniteBag(Seq(StringLiteral("a") -> int(1)), StringType())) {
      e"Bag[String]('a' -> 1)"
    }

    val b1 = FiniteBag(Seq(int(1) -> int(1)), IntegerType())
    val b2 = FiniteBag(Seq(int(2) -> int(1)), IntegerType())
    assertResult(MultiplicityInBag(int(1), b1)) { e"multiplicity({1 -> 1}, 1)" }
    assertResult(BagAdd(b1, int(2))) { e"bagAdd({1 -> 1}, 2)" }
    assertResult(BagUnion(b1, b2)) { e"bagUnion({1 -> 1}, {2 -> 1})" }
    assertResult(BagIntersection(b1, b2)) { e"bagIntersection({1 -> 1}, {2 -> 1})" }
    assertResult(BagDifference(b1, b2)) { e"bagDifference({1 -> 1}, {2 -> 1})" }
  }

  test("Parsing maps") {
    assertResult(FiniteMap(Seq(), Int32Literal(42), IntegerType(), Int32Type())) {
      e"{*: BigInt -> 42} : Map[BigInt, Int]"
    }
    assertResult(FiniteMap(Seq(StringLiteral("a") -> StringLiteral("A")), StringLiteral("?"), StringType(), StringType())) {
      e"{* -> '?', 'a' -> 'A'}"
    }
    assertResult(FiniteMap(Seq(int(1) -> BooleanLiteral(true)), BooleanLiteral(false), IntegerType(), BooleanType())) {
      e"Map(false, 1 -> true)"
    }
    assertResult(FiniteMap(Seq(int(1) -> BooleanLiteral(true)), BooleanLiteral(false), IntegerType(), BooleanType())) {
      e"Map[BigInt, Boolean](false, 1 -> true)"
    }

    val m = FiniteMap(Seq(), BooleanLiteral(false), IntegerType(), BooleanType())
    assertResult(MapApply(m, int(1))) { e"apply({*: BigInt -> false}, 1)" }
    assertResult(MapUpdated(m, int(1), BooleanLiteral(true))) { e"updated({*: BigInt -> false}, 1, true)" }
  }

  test("Parsing tuples") {
    assertResult(Tuple(Seq(int(1), BooleanLiteral(true)))) {
      e"(1, true)"
    }
    assertResult(Tuple(Seq(int(1), StringLiteral("a"), UnitLiteral()))) {
      e"(1, 'a', ())"
    }
    assertResult(TupleSelect(Tuple(Seq(int(1), BooleanLiteral(true))), 2)) {
      e"(1, true)._2"
    }
    assert(e"lambda x: (BigInt, String). x._2".getType ==
      FunctionType(Seq(TupleType(Seq(IntegerType(), StringType()))), StringType()))
  }

  test("Parsing bit-vector operations") {
    assertResult(BVAnd(Int32Literal(1), Int32Literal(2))) { e"(1 : Int) & 2" }
    assertResult(BVOr(Int32Literal(1), Int32Literal(2))) { e"(1 : Int) | 2" }
    assertResult(BVXor(Int32Literal(1), Int32Literal(2))) { e"(1 : Int) ^ 2" }
    assertResult(BVShiftLeft(Int32Literal(1), Int32Literal(2))) { e"(1 : Int) << 2" }
    assertResult(BVAShiftRight(Int32Literal(1), Int32Literal(2))) { e"(1 : Int) >> 2" }
    assertResult(BVLShiftRight(Int32Literal(1), Int32Literal(2))) { e"(1 : Int) >>> 2" }
    assertResult(BVNot(Int32Literal(1))) { e"~(1 : Int)" }
    assertResult(BVLiteral(true, 5, 12)) { e"5 : Int12" }
    assertResult(BVLiteral(false, 5, 7)) { e"5 : UInt7" }
    assertResult(Remainder(Int8Literal(7), Int8Literal(2))) { e"(7 : Int8) % 2" }
    assertResult(Modulo(int(7), int(2))) { e"7 mod 2" }
    assertResult(UMinus(Int16Literal(7))) { e"-(7 : Int16)" }
    assert(e"1 : Int64".getType == Int64Type())
  }

  test("Parsing reals") {
    assertResult(FractionLiteral(15, 4)) { e"3.75" }
    assertResult(FractionLiteral(1, 3)) { e"0.(3)" }
    assertResult(FractionLiteral(7, 6)) { e"1.1(6)" }
    assertResult(Division(FractionLiteral(1, 1), FractionLiteral(2, 1))) { e"1 / (2 : Real)" }
  }

  test("Parsing let bindings") {
    e"let x: BigInt = 1 in x + x" match {
      case Let(vd, IntegerLiteral(one), Plus(v1: Variable, v2: Variable)) =>
        assert(one == 1 && vd.id.name == "x" && vd.tpe == IntegerType())
        assert(v1 == vd.toVariable && v2 == vd.toVariable)
      case e => fail(s"Unexpected $e")
    }

    e"let x = 'a' in length(x)" match {
      case Let(vd, s: StringLiteral, StringLength(v)) if s.value == Seq('a'.toInt) =>
        assert(vd.tpe == StringType() && v == vd.toVariable)
      case e => fail(s"Unexpected $e")
    }

    e"let x = 1 in let y = x + 1 in y * x" match {
      case Let(x, _, Let(y, Plus(x1, _), Times(y1, x2))) =>
        assert(x1 == x.toVariable && x2 == x.toVariable && y1 == y.toVariable)
      case e => fail(s"Unexpected $e")
    }
  }

  test("Parsing conditionals and assumptions") {
    assertResult(IfExpr(BooleanLiteral(true), int(1), int(2))) {
      e"if (true) 1 else 2"
    }
    assertResult(IfExpr(BooleanLiteral(true), int(1), IfExpr(BooleanLiteral(false), int(2), int(3)))) {
      e"if (true) 1 else if (false) 2 else 3"
    }
    assertResult(Assume(BooleanLiteral(true), int(1))) {
      e"assume(true) in 1"
    }
  }

  test("Parsing lambdas and applications") {
    e"lambda x: BigInt, y: BigInt. x + y" match {
      case Lambda(Seq(x, y), Plus(vx, vy)) =>
        assert(x.toVariable == vx && y.toVariable == vy)
        assert(x.tpe == IntegerType() && y.tpe == IntegerType())
      case e => fail(s"Unexpected $e")
    }

    e"λx. x ++ 'a'" match {
      case Lambda(Seq(x), StringConcat(vx, s: StringLiteral)) if s.value == Seq('a'.toInt) =>
        assert(x.tpe == StringType() && vx == x.toVariable)
      case e => fail(s"Unexpected $e")
    }

    e"(lambda x: BigInt. x + 1)(2)" match {
      case Application(Lambda(Seq(x), _), Seq(IntegerLiteral(two))) =>
        assert(two == 2)
      case e => fail(s"Unexpected $e")
    }

    e"let f = lambda x: BigInt, y: Boolean. if (y) x else 0 in f(1, true)" match {
      case Let(f, _: Lambda, Application(vf, Seq(IntegerLiteral(_), BooleanLiteral(true)))) =>
        assert(f.tpe == FunctionType(Seq(IntegerType(), BooleanType()), IntegerType()))
        assert(vf == f.toVariable)
      case e => fail(s"Unexpected $e")
    }
  }

  test("Parsing quantifiers") {
    e"forall x: BigInt, y: BigInt. x + y == y + x" match {
      case Forall(Seq(x, y), Equals(Plus(vx, vy), Plus(vy2, vx2))) =>
        assert(vx == x.toVariable && vx2 == x.toVariable && vy == y.toVariable && vy2 == y.toVariable)
      case e => fail(s"Unexpected $e")
    }

    e"exists x: Int. x > 0" match {
      case Not(Forall(Seq(x), Not(GreaterThan(vx, Int32Literal(zero))))) =>
        assert(x.tpe == Int32Type() && vx == x.toVariable && zero == 0)
      case e => fail(s"Unexpected $e")
    }

    e"∃x, y. x + y == (0 : Real)" match {
      case Not(Forall(Seq(x, y), _)) =>
        assert(x.tpe == RealType() && y.tpe == RealType())
      case e => fail(s"Unexpected $e")
    }
  }

  test("Parsing type annotations and embedded values") {
    val x = Variable.fresh("x", IntegerType())
    val tpe = SetType(IntegerType())
    assertResult(Plus(x, int(1))) { e"$x + 1" }
    assertResult(FiniteSet(Seq(), IntegerType())) { e"{} : $tpe" }
    assertResult(Plus(Int32Literal(3), Int32Literal(1))) { e"${3} + 1" }
    assertResult(Plus(x, int(3))) { e"$x + ${BigInt(3)}" }
    assertResult(StringConcat(StringLiteral("a"), StringLiteral("b"))) { e"${"a"} ++ 'b'" }
    assertResult(And(BooleanLiteral(true), BooleanLiteral(false))) { e"${true} && false" }
    assertResult(Plus(Int32Literal(1), Int32Literal(2))) { e"${1: Int} + (2 : Int)" }
    assertResult(Equals(CharLiteral('a'), CharLiteral('b'))) { e"${'a'} == ${'b'}" }
    assertResult(Equals(UnitLiteral(), UnitLiteral())) { e"${()} == ()" }
    assert(e"lambda y. ${x} + y".getType == FunctionType(Seq(IntegerType()), IntegerType()))
  }

  test("Parsing value definitions") {
    val vd = v"x: Set[BigInt]"
    assert(vd.id.name == "x" && vd.tpe == SetType(IntegerType()))
  }

  test("Lexing") {
    val tokens = r"lambda x. x + 1"
    assert(tokens.nonEmpty)
    assert(tokens.map(_.toString).mkString(" ").contains("lambda"))
  }

  test("Parsing types") {
    assert(t"Set[(BigInt, String)]" == SetType(TupleType(Seq(IntegerType(), StringType()))))
    assert(t"Bag[Char]" == BagType(CharType()))
    assert(t"Map[Int, Boolean]" == MapType(Int32Type(), BooleanType()))
    assert(t"(BigInt, Real) => Unit" == FunctionType(Seq(IntegerType(), RealType()), UnitType()))
    assert(t"Int => Int => Int" == FunctionType(Seq(Int32Type()), FunctionType(Seq(Int32Type()), Int32Type())))
    assert(t"Int64" == Int64Type())
    assert(t"UInt16" == BVType(false, 16))
  }

  test("Parsing errors") {
    def fails(body: => Any): Unit = {
      val ex = intercept[Exception](body)
      assert(ex.getMessage != null && ex.getMessage.nonEmpty)
    }
    fails(e"1 +")
    fails(e"if (true) 1")
    fails(e"let x = 1 x")
    fails(e"lambda . x")
    fails(e"1 + true")
    fails(e"unknownFunction(1)")
    fails(e"length(1)")
    fails(e"{1, 'a'}")
    fails(t"Set[")
    fails(t"NotAType")
    fails(e"(1, 2)._3")
    fails(e"x + 1")
  }
}
