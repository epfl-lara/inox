/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package parsing

import org.scalatest.funsuite.AnyFunSuite

/** Matching expressions against `e"..."` patterns, operation by operation, in a program with
  * a polymorphic function and sort. */
class ExpressionExtractorSuite extends AnyFunSuite {

  import inox.trees.{given, _}
  import inox.trees.dsl._
  import interpolator.{given, _}

  // def id[T](x: T): T = x
  val idID = FreshIdentifier("id")
  val idFd = mkFunDef(idID)("T") { case Seq(t) => (Seq("x" :: t), t, { case Seq(x) => x }) }
  // case class MkBox[T](value: T)
  val boxID = FreshIdentifier("Box")
  val mkBoxID = FreshIdentifier("MkBox")
  val valueID = FreshIdentifier("value")
  val boxSort = mkSort(boxID)("T") { case Seq(t) => Seq((mkBoxID, Seq(ValDef(valueID, t)))) }

  given Symbols = NoSymbols.withFunctions(Seq(idFd)).withSorts(Seq(boxSort))

  val x = Variable.fresh("x", IntegerType())
  val y = Variable.fresh("y", IntegerType())
  val p = Variable.fresh("p", BooleanType())
  val q = Variable.fresh("q", BooleanType())
  val bag = Variable.fresh("bag", BagType(IntegerType()))
  val map = Variable.fresh("map", MapType(IntegerType(), BooleanType()))
  val box = Variable.fresh("box", ADTType(boxID, Seq(IntegerType())))

  test("Matching function invocations") {
    val call = FunctionInvocation(idID, Seq(IntegerType()), Seq(x))
    call match {
      case e"id($a)" => assert(a == x)
      case _ => fail("Did not match.")
    }
    call match {
      case e"id[Int]($a)" => fail("Did match.")
      case e"id[BigInt]($a)" => assert(a == x)
      case _ => fail("Did not match.")
    }
    call match {
      case e"$f[Boolean]($a)" => fail("Did match.")
      case e"$f[BigInt]($a)" => assert(f == idID && a == x)
      case _ => fail("Did not match.")
    }
    call match {
      case e"$f($a, $b)" => fail("Did match.")
      case e"$f($a)" => assert(f == idID && a == x)
      case _ => fail("Did not match.")
    }
  }

  test("Matching constructors and selectors") {
    val cons = ADT(mkBoxID, Seq(IntegerType()), Seq(x))
    cons match {
      case e"MkBox($a)" => assert(a == x)
      case _ => fail("Did not match.")
    }
    cons match {
      case e"MkBox[Boolean]($a)" => fail("Did match.")
      case e"MkBox[BigInt]($a)" => assert(a == x)
      case _ => fail("Did not match.")
    }
    cons match {
      case e"$c[BigInt]($a)" => assert(c == mkBoxID && a == x)
      case _ => fail("Did not match.")
    }
    cons match {
      case e"$c($a)" => assert(c == mkBoxID && a == x)
      case _ => fail("Did not match.")
    }
    ADTSelector(box, valueID) match {
      case e"$b.value" => assert(b == box)
      case _ => fail("Did not match.")
    }
    ADTSelector(box, valueID) match {
      case e"$b.$f" => assert(b == box && f == valueID)
      case _ => fail("Did not match.")
    }
    IsConstructor(box, mkBoxID) match {
      case e"$b is MkBox" => assert(b == box)
      case _ => fail("Did not match.")
    }
  }

  test("Matching literals") {
    CharLiteral('a') match {
      case e"`b`" => fail("Did match.")
      case e"`a`" => succeed
      case _ => fail("Did not match.")
    }
    UnitLiteral() match {
      case e"()" => succeed
      case _ => fail("Did not match.")
    }
    BooleanLiteral(false) match {
      case e"true" => fail("Did match.")
      case e"false" => succeed
      case _ => fail("Did not match.")
    }
    FractionLiteral(3, 2) match {
      case e"1.25" => fail("Did match.")
      case e"1.5" => succeed
      case _ => fail("Did not match.")
    }
    FractionLiteral(4, 1) match {
      case e"4" => succeed
      case _ => fail("Did not match.")
    }
  }

  test("Matching boolean operations") {
    And(p, q) match {
      case e"$a || $b" => fail("Did match.")
      case e"$a && $b" => assert(a == p && b == q)
      case _ => fail("Did not match.")
    }
    Or(p, q) match {
      case e"$a && $b" => fail("Did match.")
      case e"$a || $b" => assert(a == p && b == q)
      case _ => fail("Did not match.")
    }
    Implies(p, q) match {
      case e"$a ==> $b" => assert(a == p && b == q)
      case _ => fail("Did not match.")
    }
    Not(p) match {
      case e"!$a" => assert(a == p)
      case _ => fail("Did not match.")
    }
  }

  test("Matching arithmetic and comparisons") {
    UMinus(x) match {
      case e"-$a" => assert(a == x)
      case _ => fail("Did not match.")
    }
    Remainder(x, y) match {
      case e"$a % $b" => assert(a == x && b == y)
      case _ => fail("Did not match.")
    }
    Modulo(x, y) match {
      case e"$a mod $b" => assert(a == x && b == y)
      case _ => fail("Did not match.")
    }
    LessThan(x, y) match {
      case e"$a < $b" => assert(a == x && b == y)
      case _ => fail("Did not match.")
    }
    GreaterThan(x, y) match {
      case e"$a > $b" => assert(a == x && b == y)
      case _ => fail("Did not match.")
    }
    LessEquals(x, y) match {
      case e"$a <= $b" => assert(a == x && b == y)
      case _ => fail("Did not match.")
    }
    GreaterEquals(x, y) match {
      case e"$a >= $b" => assert(a == x && b == y)
      case _ => fail("Did not match.")
    }
  }

  test("Matching bags and maps with types") {
    BagAdd(bag, x) match {
      case e"bagAdd[BigInt]($b, $e)" => assert(b == bag && e == x)
      case _ => fail("Did not match.")
    }
    BagIntersection(bag, bag) match {
      case e"bagIntersection($a, $b)" => assert(a == bag && b == bag)
      case _ => fail("Did not match.")
    }
    BagDifference(bag, bag) match {
      case e"bagDifference($a, $b)" => assert(a == bag && b == bag)
      case _ => fail("Did not match.")
    }
    MapApply(map, x) match {
      case e"apply[BigInt, Int]($m, $k)" => fail("Did match.")
      case e"apply[BigInt, Boolean]($m, $k)" => assert(m == map && k == x)
      case _ => fail("Did not match.")
    }
    MapUpdated(map, x, p) match {
      case e"updated[BigInt, Boolean]($m, $k, $v)" => assert(m == map && k == x && v == p)
      case _ => fail("Did not match.")
    }
    val finite = FiniteMap(Seq(IntegerLiteral(1) -> BooleanLiteral(true)), BooleanLiteral(false), IntegerType(), BooleanType())
    finite match {
      case e"Map[BigInt, Boolean]($d, 1 -> $v)" => assert(d == BooleanLiteral(false) && v == BooleanLiteral(true))
      case _ => fail("Did not match.")
    }
    finite match {
      case e"{*: BigInt -> $d, 1 -> true}" => assert(d == BooleanLiteral(false))
      case _ => fail("Did not match.")
    }
  }

  test("Matching binders") {
    e"let a: BigInt = 1, b: BigInt = 2 in a + b" match {
      case e"let a: BigInt = $u, b: BigInt = $v in a + b" => assert(u == IntegerLiteral(1) && v == IntegerLiteral(2))
      case _ => fail("Did not match.")
    }
    val lambda = Lambda(Seq(x.toVal), Plus(x, IntegerLiteral(1)))
    lambda match {
      case e"lambda $v: BigInt. $body" => assert(v == x.id && body == Plus(x, IntegerLiteral(1)))
      case _ => fail("Did not match.")
    }
    lambda match {
      case e"lambda a: BigInt, b: BigInt. $body" => fail("Did match.")
      case _ => succeed
    }
  }

  test("Matching argument lists of the wrong length") {
    val f = Variable.fresh("f", FunctionType(Seq(), IntegerType()))
    Application(f, Seq()) match {
      case e"$g(1)" => fail("Did match.")
      case e"$g()" => assert(g == f)
      case _ => fail("Did not match.")
    }
    val h = Variable.fresh("h", FunctionType(Seq(IntegerType()), IntegerType()))
    Application(h, Seq(x)) match {
      case e"$g()" => fail("Did match.")
      case e"$g($a)" => assert(g == h && a == x)
      case _ => fail("Did not match.")
    }
  }

  test("Expressions don't match patterns of another kind") {
    val set = Variable.fresh("set", SetType(IntegerType()))
    val bv = Variable.fresh("bv", BVType(true, 32))
    val s = Variable.fresh("s", StringType())
    val exprs = Seq(
      x, IfExpr(p, x, y), Assume(p, x), Let(x.toVal, y, x), Lambda(Seq(x.toVal), x), Forall(Seq(x.toVal), p),
      exprOps.uninterpretedCall("u", Seq(), Seq(x.toVal), IntegerType()), Application(Variable.fresh("f", FunctionType(Seq(), IntegerType())), Seq()),
      FunctionInvocation(idID, Seq(IntegerType()), Seq(x)), ADT(mkBoxID, Seq(IntegerType()), Seq(x)),
      ADTSelector(box, valueID), IsConstructor(box, mkBoxID), Tuple(Seq(x, y)), TupleSelect(Tuple(Seq(x, y)), 1),
      CharLiteral('a'), UnitLiteral(), Equals(x, y), BooleanLiteral(true), And(p, q), Or(p, q), Implies(p, q), Not(p),
      StringLiteral("a"), StringConcat(s, s), SubString(s, x, y), StringLength(s),
      IntegerLiteral(1), FractionLiteral(1, 2), Plus(x, y), Minus(x, y), Times(x, y), Division(x, y), UMinus(x),
      Remainder(x, y), Modulo(x, y), LessThan(x, y), GreaterThan(x, y), LessEquals(x, y), GreaterEquals(x, y),
      BVLiteral(true, 1, 32), BVNot(bv), BVOr(bv, bv), BVAnd(bv, bv), BVXor(bv, bv), BVShiftLeft(bv, bv),
      BVAShiftRight(bv, bv), BVLShiftRight(bv, bv),
      FiniteSet(Seq(x), IntegerType()), SetAdd(set, x), ElementOfSet(x, set), SubsetOf(set, set), SetUnion(set, set),
      SetIntersection(set, set), SetDifference(set, set),
      FiniteBag(Seq(x -> y), IntegerType()), BagAdd(bag, x), MultiplicityInBag(x, bag), BagIntersection(bag, bag),
      BagUnion(bag, bag), BagDifference(bag, bag),
      FiniteMap(Seq(), p, IntegerType(), BooleanType()), MapApply(map, x), MapUpdated(map, x, p),
      Int8Literal(1)
    )
    for (expr <- exprs) expr match {
      case e"`z`" => fail(s"$expr matched a character literal.")
      case _ => succeed
    }
  }

  test("Matching types") {
    BVType(true, 8) match {
      case t"Int16" => fail("Did match.")
      case t"UInt8" => fail("Did match.")
      case t"Int8" => succeed
      case _ => fail("Did not match.")
    }
    Untyped match {
      case t"BigInt" => fail("Did match.")
      case _ => succeed
    }
    ADTType(boxID, Seq(IntegerType())) match {
      case t"$b[Boolean]" => fail("Did match.")
      case t"$b[BigInt]" => assert(b == boxID)
      case _ => fail("Did not match.")
    }
    TupleType(Seq(IntegerType(), BooleanType())) match {
      case t"(BigInt, Boolean, $c)" => fail("Did match.")
      case t"(BigInt, Boolean)" => succeed
      case _ => fail("Did not match.")
    }
    FunctionType(Seq(IntegerType()), BooleanType()) match {
      case t"() => $b" => fail("Did match.")
      case t"(BigInt) => $b" => assert(b == BooleanType())
      case _ => fail("Did not match.")
    }

    val n = ValDef(FreshIdentifier("n"), IntegerType())
    val m = ValDef(FreshIdentifier("m"), BooleanType())
    SigmaType(Seq(n), IntegerType()) match {
      case t"(n: Boolean, BigInt)" => fail("Did match.")
      case t"(n: BigInt, $b)" => assert(b == IntegerType())
      case _ => fail("Did not match.")
    }
    val pi = PiType(Seq(n, m), IntegerType())
    pi match {
      case t"(n: BigInt) => $b" => fail("Did match.")
      case t"(n: BigInt, m: Boolean, k: BigInt) => $b" => fail("Did match.")
      case t"(n: BigInt, Boolean) => $b" => fail("Did match.")
      case t"(n: BigInt, m: Boolean) => $b" => assert(b == IntegerType())
      case _ => fail("Did not match.")
    }
    pi match {
      case t"(n: BigInt, $ps...) => $b" => assert(ps == Seq(m) && b == IntegerType())
      case _ => fail("Did not match.")
    }
    pi match {
      case t"(n: BigInt, m: Boolean, $ps...) => $b" => assert(ps == Seq() && b == IntegerType())
      case _ => fail("Did not match.")
    }
  }
}
