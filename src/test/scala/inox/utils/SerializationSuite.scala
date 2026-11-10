/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package utils

import org.scalatest.funsuite.AnyFunSuite

class SerializationSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._

  private val serializer = Serializer(inox.trees)
  import serializer.given

  private def roundTrip[T](value: T)(using serializer.SerializationProcedure[T]): T =
    serializer.deserialize[T](serializer.serialize(value))

  test("Primitive values") {
    assert(roundTrip(true) == true)
    assert(roundTrip('x') == 'x')
    assert(roundTrip((-3).toByte) == (-3).toByte)
    assert(roundTrip((-300).toShort) == (-300).toShort)
    assert(roundTrip(Int.MinValue) == Int.MinValue)
    assert(roundTrip(Long.MaxValue) == Long.MaxValue)
    assert(roundTrip(BigInt("-123456789012345678901234567890")) == BigInt("-123456789012345678901234567890"))
    assert(roundTrip(1.5f) == 1.5f)
    assert(roundTrip(-0d).equals(-0d))
    assert(roundTrip(Double.NaN).isNaN)
  }

  test("Strings, including ones UTF-8 can't encode") {
    for (s <- Seq("", "abc", "é€😀", "\u0000", "\ud800", "a\udc00b", "\ude00\ud83d")) {
      assert(roundTrip(s) == s, s.map(c => f"\\u${c.toInt}%04x").mkString)
    }
  }

  test("Collections") {
    assert(roundTrip(Option(1)) == Some(1))
    assert(roundTrip(Option.empty[Int]) == None)
    assert(roundTrip(Seq(1, 2, 3)) == Seq(1, 2, 3))
    assert(roundTrip(Set("a", "b")) == Set("a", "b"))
    assert(roundTrip(Map(1 -> "a", 2 -> "b")) == Map(1 -> "a", 2 -> "b"))
    assert(roundTrip((1, "a")) == (1, "a"))
    assert(roundTrip((1, "a", true)) == (1, "a", true))
    assert(roundTrip((1, "a", true, 'c')) == (1, "a", true, 'c'))
    assert(roundTrip(Map(Set(1) -> Seq(Option(2)))) == Map(Set(1) -> Seq(Option(2))))
  }

  test("Sets and maps serialize the same way whatever their order") {
    // Serialized trees are used as cache keys, so equal values must give equal bytes
    val elems = (1 to 50).map(i => s"e$i")
    assert(serializer.serialize(elems.toSet) == serializer.serialize(elems.reverse.toSet))
    val pairs = elems.zipWithIndex
    assert(serializer.serialize(pairs.toMap) == serializer.serialize(pairs.reverse.toMap))
  }

  test("Identifiers keep their global id") {
    val id = FreshIdentifier("x")
    val back = roundTrip(id)
    assert(back == id)
    assert(back.globalId == id.globalId)
    assert(back.id == id.id)
  }

  test("Fresh identifiers never take the global id of a deserialized one") {
    // Identifiers from another process can have global ids that this one hasn't handed out yet
    val bytes = serializer.serialize(new Identifier("y", FreshIdentifier("z").globalId + 1000, 0))
    val restored = serializer.deserialize[Identifier](bytes)
    val fresh = Seq.fill(1001)(FreshIdentifier("y"))
    assert(!fresh.contains(restored))
  }

  test("Floating point and bit-vector literals") {
    for (f <- Seq(0f, -0f, 1.4f, Float.NaN, Float.NegativeInfinity, Float.MinPositiveValue)) {
      assert(roundTrip[Expr](Float32Literal(f)) == Float32Literal(f))
    }
    for (d <- Seq(-0d, Double.MaxValue, Double.NaN)) {
      assert(roundTrip[Expr](Float64Literal(d)) == Float64Literal(d))
    }
    for (lit <- Seq(Int8Literal(-128), Int64Literal(Long.MinValue), BVLiteral(false, BigInt(5), 3))) {
      assert(roundTrip[Expr](lit) == lit)
    }
  }

  test("Types") {
    val tp = TypeParameter.fresh("T")
    val x = ValDef.fresh("x", IntegerType())
    val types: Seq[Type] = Seq(
      Untyped, BooleanType(), UnitType(), CharType(), IntegerType(), RealType(), StringType(),
      BVType(true, 7), FPType(11, 53), RoundingMode, tp, TupleType(Seq(IntegerType(), tp)),
      SetType(tp), BagType(tp), MapType(IntegerType(), BooleanType()), FunctionType(Seq(tp), tp),
      ADTType(FreshIdentifier("List"), Seq(tp)), RefinementType(x, x.toVariable > E(BigInt(0))),
      PiType(Seq(x), RefinementType(ValDef.fresh("y", IntegerType()), E(true))),
      SigmaType(Seq(x), IntegerType()),
    )
    for (t <- types) assert(roundTrip(t) == t, t.toString)
  }

  test("Expressions with binders, collections and flags") {
    val x = ValDef.fresh("x", IntegerType())
    val m = Variable.fresh("m", MapType(IntegerType(), IntegerType()))
    val exprs: Seq[Expr] = Seq(
      Lambda(Seq(x), x.toVariable + E(BigInt(1))),
      Forall(Seq(x), x.toVariable * x.toVariable >= E(BigInt(0))),
      exprOps.choose(x, x.toVariable > E(BigInt(3))),
      Let(x, E(BigInt(2)), Tuple(Seq(x.toVariable, E("s")))),
      FiniteSet(Seq(E(BigInt(1)), E(BigInt(2))), IntegerType()),
      FiniteBag(Seq(E(BigInt(1)) -> E(BigInt(2))), IntegerType()),
      FiniteMap(Seq(E(BigInt(1)) -> E(BigInt(2))), E(BigInt(0)), IntegerType(), IntegerType()),
      MapMerge(FiniteSet(Seq(E(BigInt(1))), IntegerType()), m, m),
      FPRound(RoundNearestTiesToAway, Float64Literal(2.5)),
      Variable(FreshIdentifier("a"), IntegerType(), Seq(Annotation("note", Seq("text", BigInt(1), Seq(true))))),
    )
    for (e <- exprs) assert(roundTrip(e) == e, e.toString)
  }

  test("Definitions") {
    val tp = TypeParameter.fresh("T")
    val listId = FreshIdentifier("List")
    val consId = FreshIdentifier("Cons")
    val nilId = FreshIdentifier("Nil")
    val invId = FreshIdentifier("inv")
    val head = ValDef(FreshIdentifier("head"), tp)
    val tail = ValDef(FreshIdentifier("tail"), ADTType(listId, Seq(tp)))
    val sort = new ADTSort(listId, Seq(TypeParameterDef(tp)),
      Seq(new ADTConstructor(consId, listId, Seq(head, tail)), new ADTConstructor(nilId, listId, Seq())),
      Seq(HasADTInvariant(invId), HasADTEquality(FreshIdentifier("eq"))))

    val back = roundTrip(sort)
    assert(back.id == sort.id)
    assert(back.tparams == sort.tparams)
    assert(back.constructors == sort.constructors)
    assert(back.constructors.map(_.fields) == sort.constructors.map(_.fields))
    assert(back.flags == sort.flags)

    val l = ValDef.fresh("l", ADTType(listId, Seq(tp)))
    val fd = new FunDef(invId, Seq(TypeParameterDef(tp)), Seq(l), BooleanType(),
      IsConstructor(l.toVariable, consId) || IsConstructor(l.toVariable, nilId), Seq(Annotation("inline", Seq())))
    val fdBack = roundTrip(fd)
    assert(fdBack.id == fd.id)
    assert(fdBack.tparams == fd.tparams)
    assert(fdBack.params == fd.params)
    assert(fdBack.returnType == fd.returnType)
    assert(fdBack.fullBody == fd.fullBody)
    assert(fdBack.flags == fd.flags)
  }

  test("Serialization results nest") {
    val inner = serializer.serialize(Seq(1, 2))
    assert(roundTrip(inner) == inner)
  }

  test("Class serializers have distinct ids") {
    class Ids extends InoxSerializer(inox.trees) {
      def ids: Seq[Int] = classSerializers.values.toSeq.map(_.id)
    }
    val ids = new Ids().ids
    assert(ids.diff(ids.distinct).isEmpty, s"duplicated ids: ${ids.diff(ids.distinct).distinct.sorted}")
  }

  test("Values without a serializer are rejected") {
    case class Unknown(i: Int)
    assertThrows[SerializationError] {
      serializer.serialize[Expr](Variable(FreshIdentifier("a"), IntegerType(), Seq(Annotation("note", Seq(Unknown(1))))))
    }
  }
}
