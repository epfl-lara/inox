/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package parsing

import org.scalatest.funsuite.AnyFunSuite

/** Matching expressions and types against `e"..."` and `t"..."` patterns. */
class PrimitivesExtractorSuite extends AnyFunSuite {

  import inox.trees.{given, _}
  import interpolator.{given, _}
  given Symbols = NoSymbols

  val x = Variable.fresh("x", IntegerType())
  val s = Variable.fresh("s", StringType())
  val set = Variable.fresh("set", SetType(IntegerType()))
  val bag = Variable.fresh("bag", BagType(IntegerType()))
  val map = Variable.fresh("map", MapType(IntegerType(), BooleanType()))

  test("Matching strings") {
    StringConcat(s, StringLiteral("a")) match {
      case e"$y ++ 'b'" => fail("Did match.")
      case e"$y ++ 'a'" => assert(y == s)
      case _ => fail("Did not match.")
    }
    StringLength(s) match {
      case e"length($y)" => assert(y == s)
      case _ => fail("Did not match.")
    }
    SubString(s, IntegerLiteral(1), x) match {
      case e"substring($y, 1, $z)" => assert(y == s && z == x)
      case _ => fail("Did not match.")
    }
  }

  test("Matching sets") {
    FiniteSet(Seq(IntegerLiteral(1), x), IntegerType()) match {
      case e"{1, 2}" => fail("Did match.")
      case e"{1, $y}" => assert(y == x)
      case _ => fail("Did not match.")
    }
    ElementOfSet(x, set) match {
      case e"contains($a, $b)" => assert(a == set && b == x)
      case _ => fail("Did not match.")
    }
    ElementOfSet(x, set) match {
      case e"$a ∈ $b" => assert(a == x && b == set)
      case _ => fail("Did not match.")
    }
    SetUnion(set, set) match {
      case e"$a ∩ $b" => fail("Did match.")
      case e"$a ∪ $b" => assert(a == set && b == set)
      case _ => fail("Did not match.")
    }
    SetIntersection(set, set) match {
      case e"intersection($a, $b)" => assert(a == set && b == set)
      case _ => fail("Did not match.")
    }
    SetDifference(set, set) match {
      case e"$a ∖ $b" => assert(a == set && b == set)
      case _ => fail("Did not match.")
    }
    SubsetOf(set, set) match {
      case e"$a ⊆ $b" => assert(a == set && b == set)
      case _ => fail("Did not match.")
    }
    SetAdd(set, x) match {
      case e"add($a, $b)" => assert(a == set && b == x)
      case _ => fail("Did not match.")
    }
  }

  test("Matching bags and maps") {
    FiniteBag(Seq(x -> IntegerLiteral(2)), IntegerType()) match {
      case e"{$k -> $v}" => assert(k == x && v == IntegerLiteral(2))
      case _ => fail("Did not match.")
    }
    MultiplicityInBag(x, bag) match {
      case e"multiplicity($b, $k)" => assert(b == bag && k == x)
      case _ => fail("Did not match.")
    }
    BagUnion(bag, bag) match {
      case e"bagIntersection($a, $b)" => fail("Did match.")
      case e"bagUnion($a, $b)" => assert(a == bag && b == bag)
      case _ => fail("Did not match.")
    }
    MapApply(map, x) match {
      case e"apply($m, $k)" => assert(m == map && k == x)
      case _ => fail("Did not match.")
    }
    MapUpdated(map, x, BooleanLiteral(true)) match {
      case e"updated($m, $k, $v)" => assert(m == map && k == x && v == BooleanLiteral(true))
      case _ => fail("Did not match.")
    }
    FiniteMap(Seq(IntegerLiteral(1) -> BooleanLiteral(true)), BooleanLiteral(false), IntegerType(), BooleanType()) match {
      case e"{* -> $d, 1 -> $v}" => assert(d == BooleanLiteral(false) && v == BooleanLiteral(true))
      case _ => fail("Did not match.")
    }
  }

  test("Matching tuples and conditionals") {
    Tuple(Seq(x, s)) match {
      case e"($a, $b)" => assert(a == x && b == s)
      case _ => fail("Did not match.")
    }
    TupleSelect(Variable.fresh("t", TupleType(Seq(IntegerType(), StringType()))), 2) match {
      case e"$t._1" => fail("Did match.")
      case e"$t._2" => succeed
      case _ => fail("Did not match.")
    }
    IfExpr(BooleanLiteral(true), x, IntegerLiteral(0)) match {
      case e"if ($c) $t else $e" =>
        assert(c == BooleanLiteral(true) && t == x && e == IntegerLiteral(0))
      case _ => fail("Did not match.")
    }
    Assume(BooleanLiteral(true), x) match {
      case e"assume($c) in $b" => assert(c == BooleanLiteral(true) && b == x)
      case _ => fail("Did not match.")
    }
  }

  test("Matching binders") {
    e"let y: BigInt = 1 in y + y" match {
      case e"let y: BigInt = $v in y * y" => fail("Did match.")
      case e"let z: BigInt = $v in z + z" => fail("Did match.")
      case e"let y: BigInt = $v in y + y" => assert(v == IntegerLiteral(1))
      case _ => fail("Did not match.")
    }
    e"lambda y: BigInt. y + 1" match {
      case e"lambda y: $t. y + $o" => assert(t == IntegerType() && o == IntegerLiteral(1))
      case _ => fail("Did not match.")
    }
    e"forall y: Int. y > 0" match {
      case e"forall y: Int. y < 0" => fail("Did match.")
      case e"forall y: Int. $body" => assert(body.isInstanceOf[GreaterThan])
      case _ => fail("Did not match.")
    }
  }

  test("Matching types") {
    SetType(IntegerType()) match {
      case t"Bag[$a]" => fail("Did match.")
      case t"Set[$a]" => assert(a == IntegerType())
      case _ => fail("Did not match.")
    }
    MapType(IntegerType(), StringType()) match {
      case t"Map[$a, $b]" => assert(a == IntegerType() && b == StringType())
      case _ => fail("Did not match.")
    }
    TupleType(Seq(IntegerType(), BooleanType())) match {
      case t"($a, $b)" => assert(a == IntegerType() && b == BooleanType())
      case _ => fail("Did not match.")
    }
    FunctionType(Seq(IntegerType()), BooleanType()) match {
      case t"$a => $b" => assert(a == IntegerType() && b == BooleanType())
      case _ => fail("Did not match.")
    }
    BagType(CharType()) match {
      case t"Bag[Char]" => succeed
      case _ => fail("Did not match.")
    }
  }

  test("Matching argument sequences") {
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType(), IntegerType(), IntegerType()), IntegerType()))
    Application(f, Seq(IntegerLiteral(1), IntegerLiteral(2), x)) match {
      case e"$g($as..., 2, $last)" => assert(g == f && as == Seq(IntegerLiteral(1)) && last == x)
      case _ => fail("Did not match.")
    }
    Application(f, Seq(IntegerLiteral(1), IntegerLiteral(2), x)) match {
      case e"$g(1, $as...)" => assert(as == Seq(IntegerLiteral(2), x))
      case _ => fail("Did not match.")
    }
    Application(f, Seq(IntegerLiteral(1))) match {
      case e"$g(1, $as..., 2)" => fail("Did match.")
      case e"$g(1, $as...)" => assert(as == Seq())
      case _ => fail("Did not match.")
    }
    val h = Variable.fresh("h", FunctionType(Seq(), IntegerType()))
    Application(h, Seq()) match {
      case e"$g($as...)" => assert(g == h && as == Seq())
      case _ => fail("Did not match.")
    }
  }

  test("Matching type sequences") {
    FunctionType(Seq(IntegerType(), BooleanType()), StringType()) match {
      case t"($as...) => $b" => assert(as == Seq(IntegerType(), BooleanType()) && b == StringType())
      case _ => fail("Did not match.")
    }
    FunctionType(Seq(), StringType()) match {
      case t"($as...) => $b" => assert(as == Seq() && b == StringType())
      case _ => fail("Did not match.")
    }
    TupleType(Seq(IntegerType(), BooleanType(), CharType())) match {
      case t"(Int, $as...)" => fail("Did match.")
      case t"(BigInt, $as...)" => assert(as == Seq(BooleanType(), CharType()))
      case _ => fail("Did not match.")
    }
  }

  test("Matching bit vector operations") {
    val a = Variable.fresh("a", BVType(true, 32))
    val b = Variable.fresh("b", BVType(true, 32))
    for (expr <- Seq(BVOr(a, b), BVAnd(a, b), BVXor(a, b), BVShiftLeft(a, b), BVAShiftRight(a, b), BVLShiftRight(a, b))) {
      val op = expr match {
        case e"$l + $r" => fail("Did match.")
        case e"$l | $r" => "|"
        case e"$l & $r" => "&"
        case e"$l ^ $r" => "^"
        case e"$l << $r" => "<<"
        case e"$l >>> $r" => ">>>"
        case e"$l >> $r" => ">>"
        case _ => fail("Did not match.")
      }
      assert(op == (expr match {
        case _: BVOr => "|"
        case _: BVAnd => "&"
        case _: BVXor => "^"
        case _: BVShiftLeft => "<<"
        case _: BVAShiftRight => ">>"
        case _: BVLShiftRight => ">>>"
        case _ => ""
      }))
    }
    BVNot(a) match {
      case e"~$y" => assert(y == a)
      case _ => fail("Did not match.")
    }
  }
}
