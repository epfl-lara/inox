/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite

class DSLSuite extends AnyFunSuite with DatastructureUtils {
  import inox.trees._
  import inox.trees.dsl._

  val x = Variable.fresh("x", IntegerType())
  val y = Variable.fresh("y", IntegerType())
  val p = Variable.fresh("p", BooleanType())
  val q = Variable.fresh("q", BooleanType())
  val s1 = Variable.fresh("s1", SetType(IntegerType()))
  val s2 = Variable.fresh("s2", SetType(IntegerType()))
  val t = Variable.fresh("t", TupleType(Seq(IntegerType(), BooleanType(), CharType(), StringType())))

  test("arithmetic, comparison and boolean operators") {
    assert(x + y == Plus(x, y))
    assert(x - y == Minus(x, y))
    assert(x * y == Times(x, y))
    assert(x % y == Modulo(x, y))
    assert(x / y == Division(x, y))
    assert(-x == UMinus(x))
    assert((x < y) == LessThan(x, y))
    assert((x <= y) == LessEquals(x, y))
    assert((x > y) == GreaterThan(x, y))
    assert((x >= y) == GreaterEquals(x, y))
    assert((x === y) == Equals(x, y))
    assert((x !== y) == Not(Equals(x, y)))
    assert((p && q) == And(p, q))
    assert((p || q) == Or(p, q))
    assert((p ==> q) == Implies(p, q))
    assert(!p == Not(p))
  }

  test("tuple selections") {
    assert(t._ts1 == TupleSelect(t, 1))
    assert(t._ts2 == TupleSelect(t, 2))
    assert(t._ts3 == TupleSelect(t, 3))
    assert(t._ts4 == TupleSelect(t, 4))
  }

  test("set operators") {
    assert(s1.subsetOf(s2) == SubsetOf(s1, s2))
    assert(s1.insert(x) == SetAdd(s1, x))
    assert((s1 ++ s2) == SetUnion(s1, s2))
    assert((s1 -- s2) == SetDifference(s1, s2))
    assert((s1 & s2) == SetIntersection(s1, s2))
    assert(s1.contains(x) == ElementOfSet(x, s1))
  }

  test("ADT selections, testers and applications") {
    val l = Variable.fresh("l", T(listID)(IntegerType()))
    assert(l.getField(head) == ADTSelector(l, head))
    assert(l.is(consID) == IsConstructor(l, consID))
    assert(l.is(Cons) == IsConstructor(l, consID))
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    assert(f(x) == Application(f, Seq(x)))
  }

  test("literals") {
    assert(E(1.toByte) == Int8Literal(1))
    assert(E(2.toShort) == Int16Literal(2))
    assert(E(3) == Int32Literal(3))
    assert(E(4L) == Int64Literal(4))
    assert(E(BigInt(5)) == IntegerLiteral(5))
    assert(E(true) == BooleanLiteral(true))
    assert(E('c') == CharLiteral('c'))
    assert(E() == UnitLiteral())
    assert(E(BigInt(1), BigInt(2)) == FractionLiteral(1, 2))
    assert(E("s") == StringLiteral("s"))
    assert(E(x, y) == Tuple(Seq(x, y)))
    assert(E(x, y, p) == Tuple(Seq(x, y, p)))
    val vd = ValDef.fresh("v", IntegerType())
    assert(E(vd) == vd.toVariable)
  }

  test("function invocations") {
    val fid = FreshIdentifier("f")
    assert(E(fid)(x, y) == FunctionInvocation(fid, Seq(), Seq(x, y)))
    assert(E(fid)(IntegerType(), BooleanType())(x) == FunctionInvocation(fid, Seq(IntegerType(), BooleanType()), Seq(x)))
    val fd = mkFunDef(fid)("A") { case Seq(a) => (Seq("a" :: a), a, { case Seq(v) => v }) }
    assert(fd(x) == FunctionInvocation(fid, Seq(), Seq(x)))
    assert(fd(IntegerType())(x) == FunctionInvocation(fid, Seq(IntegerType()), Seq(x)))
    assert(fd.tparams.size == 1 && fd.params.size == 1)
    assert(fd.fullBody == fd.params.head.toVariable)
  }

  test("conditionals, lets and generic values") {
    assert((if_ (p) (x) else_ (y)) == IfExpr(p, x, y))
    assert(ite(p, x, y) == IfExpr(p, x, y))
    val tp = TypeParameter.fresh("A")
    assert((tp ## 3) == GenericValue(tp, 3))
    val l = let("z" :: IntegerType(), x) { z => z + y }
    l match {
      case Let(vd, `x`, Plus(v: Variable, `y`)) => assert(v == vd.toVariable)
      case _ => fail(s"Unexpected let $l")
    }
  }

  test("lambdas, quantifiers and interpretations with up to four parameters") {
    val vds = (1 to 4).map(i => s"v$i" :: IntegerType())
    val vs = vds.map(_.toVariable)
    assert(\(vds(0))(a => a) == Lambda(vds.take(1), vs(0)))
    assert(\(vds(0), vds(1))((a, b) => a + b) == Lambda(vds.take(2), vs(0) + vs(1)))
    assert(\(vds(0), vds(1), vds(2))((a, b, c) => a + b + c) == Lambda(vds.take(3), vs(0) + vs(1) + vs(2)))
    assert(\(vds(0), vds(1), vds(2), vds(3))((a, b, c, d) => a + b + c + d) ==
      Lambda(vds, vs(0) + vs(1) + vs(2) + vs(3)))

    assert(forall(vds(0))(a => a >= a) == Forall(vds.take(1), vs(0) >= vs(0)))
    assert(forall(vds(0), vds(1))((a, b) => a >= b) == Forall(vds.take(2), vs(0) >= vs(1)))
    assert(forall(vds(0), vds(1), vds(2))((a, b, c) => a >= b + c) == Forall(vds.take(3), vs(0) >= vs(1) + vs(2)))
    assert(forall(vds(0), vds(1), vds(2), vds(3))((a, b, c, d) => a + b >= c + d) ==
      Forall(vds, vs(0) + vs(1) >= vs(2) + vs(3)))
  }

  test("block suspensions") {
    val b = new BlockSuspension(e => Plus(e, x))
    assert(b.in(y) == Plus(y, x))
  }

  test("types") {
    assert(T(IntegerType(), BooleanType()) == TupleType(Seq(IntegerType(), BooleanType())))
    assert(T(IntegerType(), BooleanType(), CharType()) == TupleType(Seq(IntegerType(), BooleanType(), CharType())))
    assert(T(listID)(IntegerType()) == ADTType(listID, Seq(IntegerType())))
    assert(List(IntegerType()) == ADTType(listID, Seq(IntegerType())))
    val tp = T("A")
    assert(tp.id.name == "A")

    assert((IntegerType() =>: BooleanType()) == FunctionType(Seq(IntegerType()), BooleanType()))
    assert(((IntegerType(), CharType()) =>: BooleanType()) ==
      FunctionType(Seq(IntegerType(), CharType()), BooleanType()))
    assert(((IntegerType(), CharType(), StringType()) =>: BooleanType()) ==
      FunctionType(Seq(IntegerType(), CharType(), StringType()), BooleanType()))
    assert(((IntegerType(), CharType(), StringType(), UnitType()) =>: BooleanType()) ==
      FunctionType(Seq(IntegerType(), CharType(), StringType(), UnitType()), BooleanType()))
  }

  test("dependent types with up to four parameters") {
    val vds = (1 to 4).map(i => s"v$i" :: IntegerType())
    val vs = vds.map(_.toVariable)
    def ref(e: Expr) = RefinementType("r" :: IntegerType(), e)
    def refT(es: Expr*): Type = {
      val vd = "r" :: IntegerType()
      RefinementType(vd, andJoin(es.map(e => vd.toVariable >= e)))
    }
    // The refinement types are built with a fresh variable each time, so compare their shape
    def shape(tpe: Type): Type = tpe match {
      case PiType(params, to) => PiType(params, shape(to))
      case SigmaType(params, to) => SigmaType(params, shape(to))
      case RefinementType(vd, pred) => RefinementType(vds(0), exprOps.replaceFromSymbols(Map(vd -> vs(0)), pred))
      case tpe => tpe
    }

    assert(shape(pi(vds(0))(a => refT(a))) == shape(PiType(vds.take(1), refT(vs(0)))))
    assert(shape(pi(vds(0), vds(1))((a, b) => refT(a, b))) == shape(PiType(vds.take(2), refT(vs(0), vs(1)))))
    assert(shape(pi(vds(0), vds(1), vds(2))((a, b, c) => refT(a, b, c))) ==
      shape(PiType(vds.take(3), refT(vs(0), vs(1), vs(2)))))
    assert(shape(pi(vds(0), vds(1), vds(2), vds(3))((a, b, c, d) => refT(a, b, c, d))) ==
      shape(PiType(vds, refT(vs(0), vs(1), vs(2), vs(3)))))

    assert(shape(sigma(vds(0))(a => refT(a))) == shape(SigmaType(vds.take(1), refT(vs(0)))))
    assert(shape(sigma(vds(0), vds(1))((a, b) => refT(a, b))) == shape(SigmaType(vds.take(2), refT(vs(0), vs(1)))))
    assert(shape(sigma(vds(0), vds(1), vds(2))((a, b, c) => refT(a, b, c))) ==
      shape(SigmaType(vds.take(3), refT(vs(0), vs(1), vs(2)))))
    assert(shape(sigma(vds(0), vds(1), vds(2), vds(3))((a, b, c, d) => refT(a, b, c, d))) ==
      shape(SigmaType(vds, refT(vs(0), vs(1), vs(2), vs(3)))))

    assert(refinement(vds(0))(a => a > x) == RefinementType(vds(0), vs(0) > x))
    assert(ref(BooleanLiteral(true)).isInstanceOf[RefinementType])
  }

  test("constructors and their patterns") {
    val nil = C(nilID)(IntegerType())()
    assert(nil == ADT(nilID, Seq(IntegerType()), Seq()))
    assert(C(nilID)(x) == ADT(nilID, Seq(), Seq(x)))
    assert(C(consID, Seq(IntegerType()))(x, nil) == ADT(consID, Seq(IntegerType()), Seq(x, nil)))
    assert(Cons(IntegerType())(x, nil) == ADT(consID, Seq(IntegerType()), Seq(x, nil)))
    assert(Nil() == ADT(nilID, Seq(), Seq()))

    (Cons(IntegerType())(x, nil): Expr) match {
      case C(`consID`, Seq(IntegerType()), hd, tl) =>
        assert(hd == x)
        assert(tl == nil)
      case e => fail(s"Unexpected match failure on $e")
    }
    assert(C.unapplySeq(x).isEmpty)
  }
}
