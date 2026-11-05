/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package ast

import org.scalatest.funsuite.AnyFunSuite
import inox.utils.{OffsetPosition, RangePosition}

/** Checks the printed form of each kind of tree. */
class PrinterSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import dsl._

  val x = Variable(FreshIdentifier("x"), IntegerType(), Seq.empty)
  val y = Variable(FreshIdentifier("y"), IntegerType(), Seq.empty)
  val z = Variable(FreshIdentifier("z"), IntegerType(), Seq.empty)
  val p = Variable(FreshIdentifier("p"), BooleanType(), Seq.empty)
  val q = Variable(FreshIdentifier("q"), BooleanType(), Seq.empty)
  val a = Variable(FreshIdentifier("a"), Int32Type(), Seq.empty)
  val b = Variable(FreshIdentifier("b"), Int32Type(), Seq.empty)
  val f = Variable(FreshIdentifier("f"), Float64Type(), Seq.empty)
  val g = Variable(FreshIdentifier("g"), Float64Type(), Seq.empty)
  val s = Variable(FreshIdentifier("s"), StringType(), Seq.empty)
  val set = Variable(FreshIdentifier("set"), SetType(IntegerType()), Seq.empty)
  val set2 = Variable(FreshIdentifier("set2"), SetType(IntegerType()), Seq.empty)
  val bag = Variable(FreshIdentifier("bag"), BagType(IntegerType()), Seq.empty)
  val bag2 = Variable(FreshIdentifier("bag2"), BagType(IntegerType()), Seq.empty)
  val map = Variable(FreshIdentifier("map"), MapType(IntegerType(), BooleanType()), Seq.empty)
  val map2 = Variable(FreshIdentifier("map2"), MapType(IntegerType(), BooleanType()), Seq.empty)
  val mask = Variable(FreshIdentifier("mask"), SetType(IntegerType()), Seq.empty)

  val T = TypeParameter(FreshIdentifier("T"), Seq.empty)

  val listID = FreshIdentifier("List")
  val consID = FreshIdentifier("Cons")
  val nilID = FreshIdentifier("Nil")
  val headID = FreshIdentifier("head")
  val tailID = FreshIdentifier("tail")
  val invID = FreshIdentifier("inv")

  val listSort = mkSort(listID, HasADTInvariant(invID))("A") {
    case Seq(aT) => Seq(
      (consID, Seq(ValDef(headID, aT), ValDef(tailID, ADTType(listID, Seq(aT))))),
      (nilID, Seq())
    )
  }

  val sizeID = FreshIdentifier("size")
  val sizeFd = mkFunDef(sizeID, Annotation("library", Seq.empty))("A") {
    case Seq(aT) => (
      Seq(ValDef(FreshIdentifier("l"), ADTType(listID, Seq(aT)))), IntegerType(), {
        case Seq(l) => if_ (l.is(consID)) {
          IntegerLiteral(1) + E(sizeID)(aT)(l.getField(tailID))
        } else_ {
          IntegerLiteral(0)
        }
      })
  }

  val constID = FreshIdentifier("const")
  val constFd = mkFunDef(constID)() { _ => (Seq(), IntegerType(), _ => IntegerLiteral(42)) }

  val symbols = NoSymbols.withSorts(Seq(listSort)).withFunctions(Seq(sizeFd, constFd))

  private def check(tree: Tree, expected: String, opts: PrinterOptions = PrinterOptions()): Unit =
    assert(prettyPrint(tree, opts) == expected)

  private def checkAll(cases: (Tree, String)*): Unit =
    for ((tree, expected) <- cases) check(tree, expected)

  test("Literals") {
    checkAll(
      Int8Literal(-3) -> "-3",
      Int16Literal(300) -> "300",
      Int32Literal(42) -> "42",
      Int64Literal(1L << 40) -> "1099511627776",
      BVLiteral(true, 5, 4) -> "x0101",
      BVLiteral(false, 5, 6) -> "x000101",
      Float32Literal(1.5f) -> "1.5",
      Float64Literal(-0.25) -> "-0.25",
      FPLiteral(2, 3, scala.collection.immutable.BitSet(1, 3, 4, 5)) -> "x11101",
      IntegerLiteral(BigInt("123456789012345678901234567890")) -> "123456789012345678901234567890",
      FractionLiteral(6, 1) -> "6",
      FractionLiteral(1, 3) -> "1/3",
      CharLiteral('a') -> "'a'",
      CharLiteral('\n') -> "'\\n'",
      BooleanLiteral(true) -> "true",
      UnitLiteral() -> "()",
      StringLiteral("hello") -> "\"hello\"",
      StringLiteral("a \"quoted\"\tstring") -> "\"a \\\"quoted\\\"\\tstring\"",
      GenericValue(T, 2) -> "T#2",
    )
  }

  test("Long multi-line strings are printed with triple quotes") {
    val long = "first line\n" + ("x" * 80)
    check(StringLiteral(long), "\"\"\"" + long + "\"\"\"")
    // ... unless they contain triple quotes themselves
    val quoted = "\"\"\"\n" + ("x" * 80)
    check(StringLiteral(quoted), "\"\\\"\\\"\\\"\\n" + ("x" * 80) + "\"")
  }

  test("Boolean operators") {
    checkAll(
      And(p, q) -> "p && q",
      Or(p, q) -> "p || q",
      Implies(p, q) -> "p ==> q",
      Not(p) -> "!p",
      Not(Equals(x, y)) -> "x != y",
      Equals(x, y) -> "x == y",
      And(Or(p, q), p) -> "(p || q) && p",
      Or(And(p, q), p) -> "p && q || p",
      Not(And(p, q)) -> "!(p && q)",
      Equals(And(p, q), Or(p, q)) -> "(p && q) == (p || q)",
    )
  }

  test("Unicode operators") {
    val opts = PrinterOptions(printUnicode = true)
    check(Not(p), "\u00ACp", opts)
    check(Not(Equals(x, y)), "x \u2260 y", opts)
    check(ElementOfSet(x, set), "x \u2208 set", opts)
    check(Not(ElementOfSet(x, set)), "x \u2209 set", opts)
    check(SubsetOf(set, set2), "set \u2286 set2", opts)
    check(Not(SubsetOf(set, set2)), "set \u2288 set2", opts)
    check(SetAdd(set, x), "set \u222A {x}", opts)
    check(SetUnion(set, set2), "set \u222A set2", opts)
    check(SetIntersection(set, set2), "set \u2229 set2", opts)
    check(Forall(Seq(x.toVal), x >= x), "\u2200x: BigInt. (x >= x)", opts)
  }

  test("Receivers of method calls are parenthesized when needed") {
    val t = Variable(FreshIdentifier("t"), TupleType(Seq(IntegerType(), BooleanType())), Seq.empty)
    val fun = Variable(FreshIdentifier("fun"), FunctionType(Seq(IntegerType()), IntegerType()), Seq.empty)
    checkAll(
      StringLength(StringConcat(s, s)) -> "(s + s).length",
      SubString(StringConcat(s, s), x, y) -> "(s + s).substring(x, y)",
      StringLength(s) -> "s.length",
      BVWideningCast(BVAnd(a, b), Int64Type()) -> "(a & b).toLong",
      BVNarrowingCast(Plus(a, b), Int8Type()) -> "(a + b).toByte",
      BVToInt(UMinus(a)) -> "(-a).toInt",
      BVToInt(BVNot(a)) -> "(~a).toInt",
      FPIsNaN(FPAdd(RoundNearestTiesToEven, f, g)) -> "(f + g).isNaN",
      ToFloat(FPUMinus(f)) -> "(-f).toFloat",
      ElementOfSet(x, SetUnion(set, set2)) -> "(set ++ set2).contains(x)",
      MapApply(MapUpdated(map, x, p), y) -> "map.updated(x, p)(y)",
      MultiplicityInBag(x, BagUnion(bag, bag2)) -> "(bag ++ bag2)(x)",
      Application(IfExpr(p, fun, fun), Seq(x)) -> "(if (p) {\n  fun\n} else {\n  fun\n})(x)",
      TupleSelect(t, 1) -> "t._1",
    )
  }

  test("Integer and real arithmetic") {
    checkAll(
      Plus(x, y) -> "x + y",
      Minus(x, y) -> "x - y",
      UMinus(x) -> "-x",
      Times(x, y) -> "x * y",
      Division(x, y) -> "x / y",
      Remainder(x, y) -> "x % y",
      Modulo(x, y) -> "x mod y",
      LessThan(x, y) -> "x < y",
      GreaterThan(x, y) -> "x > y",
      LessEquals(x, y) -> "x <= y",
      GreaterEquals(x, y) -> "x >= y",
      Times(Plus(x, y), z) -> "(x + y) * z",
      Plus(Times(x, y), z) -> "x * y + z",
      Minus(x, Minus(y, z)) -> "x - (y - z)",
      LessThan(Plus(x, y), z) -> "x + y < z",
    )
  }

  test("Bit-vector operations and casts") {
    checkAll(
      BVNot(a) -> "~a",
      BVXor(a, b) -> "a ^ b",
      BVOr(a, b) -> "a | b",
      BVAnd(a, b) -> "a & b",
      BVShiftLeft(a, b) -> "a << b",
      BVAShiftRight(a, b) -> "a >> b",
      BVLShiftRight(a, b) -> "a >>> b",
      BVOr(BVAnd(a, b), a) -> "a & b | a",
      BVAnd(BVOr(a, b), a) -> "(a | b) & a",
      BVNarrowingCast(a, Int8Type()) -> "a.toByte",
      BVNarrowingCast(a, Int16Type()) -> "a.toShort",
      BVNarrowingCast(Variable(FreshIdentifier("l"), Int64Type(), Seq()), Int32Type()) -> "l.toInt",
      BVNarrowingCast(a, BVType(true, 12)) -> "a.toBV(12)",
      BVWideningCast(Variable(FreshIdentifier("c"), Int8Type(), Seq()), Int16Type()) -> "c.toShort",
      BVWideningCast(a, Int64Type()) -> "a.toLong",
      BVWideningCast(a, BVType(true, 40)) -> "a.toBV(40)",
      BVUnsignedToSigned(a) -> "a.toSigned",
      BVSignedToUnsigned(a) -> "a.toUnsigned",
      BVToInt(a) -> "a.toInt",
      IntToBV(8, true, x) -> "x.toBVSigned(8)",
      IntToBV(8, false, x) -> "x.toBVUnsigned(8)",
    )
  }

  test("Floating point operations") {
    checkAll(
      FPEquals(f, g) -> "f === g",
      ToFloat(f) -> "f.toFloat",
      ToDouble(Variable(FreshIdentifier("h"), Float32Type(), Seq())) -> "h.toDouble",
      FPCast(5, 11, RoundTowardZero, f) -> "f.toFP(5, 11)",
      FPFromBinary(11, 53, Variable(FreshIdentifier("l"), Int64Type(), Seq())) -> "l.toBinaryFP(11, 53)",
      FPToBVJVM(11, 53, 8, f) -> "f.toByte",
      FPToBVJVM(11, 53, 16, f) -> "f.toShort",
      FPToBVJVM(11, 53, 32, f) -> "f.toInt",
      FPToBVJVM(11, 53, 64, f) -> "f.toLong",
      FPToBV(12, true, RoundTowardZero, f) -> "f.toSBV(12)",
      FPToBV(12, false, RoundTowardZero, f) -> "f.toUBV(12)",
      FPToReal(f) -> "f.toReal",
      FPAdd(RoundNearestTiesToEven, f, g) -> "f + g",
      FPSub(RoundNearestTiesToEven, f, g) -> "f - g",
      FPUMinus(f) -> "-f",
      FPMul(RoundNearestTiesToEven, f, g) -> "f * g",
      FPDiv(RoundNearestTiesToEven, f, g) -> "f / g",
      FPFMA(RoundNearestTiesToEven, f, g, f) -> "FMA(f, g, f)",
      FPAbs(f) -> "abs(f)",
      FPMin(f, g) -> "min(f, g)",
      FPMax(f, g) -> "max(f, g)",
      FPRound(RoundTowardPositive, f) -> "rint(f)",
      Sqrt(RoundNearestTiesToEven, f) -> "sqrt(f)",
      FPLessThan(f, g) -> "f < g",
      FPGreaterThan(f, g) -> "f > g",
      FPLessEquals(f, g) -> "f <= g",
      FPGreaterEquals(f, g) -> "f >= g",
      Not(FPLessThan(f, g)) -> "!(f < g)",
      FPMul(RoundNearestTiesToEven, FPAdd(RoundNearestTiesToEven, f, g), f) -> "(f + g) * f",
      FPAdd(RoundNearestTiesToEven, FPMul(RoundNearestTiesToEven, f, g), f) -> "f * g + f",
      FPLessThan(FPAdd(RoundNearestTiesToEven, f, g), f) -> "f + g < f",
      And(FPEquals(f, g), FPIsZero(f)) -> "f === g && f == 0",
      Not(FPEquals(f, g)) -> "!(f === g)",
      FPIsZero(f) -> "f == 0",
      FPIsNaN(f) -> "f.isNaN",
      FPIsInfinite(f) -> "f.isInfinite",
      FPIsNegative(f) -> "f.isNegative",
      FPIsPositive(f) -> "f.isPositive",
      FPIsNormal(f) -> "f.isNormal",
      FPIsSubnormal(f) -> "f.isSubnormal",
      RoundTowardZero -> "RTZ",
      RoundTowardPositive -> "RTP",
      RoundTowardNegative -> "RTN",
      RoundNearestTiesToEven -> "RNE",
      RoundNearestTiesToAway -> "RNA",
    )
  }

  test("Strings") {
    checkAll(
      StringConcat(s, StringLiteral("!")) -> "s + \"!\"",
      StringConcat(StringConcat(s, s), s) -> "s + s + s",
      SubString(s, IntegerLiteral(1), IntegerLiteral(2)) -> "s.substring(1, 2)",
      StringLength(s) -> "s.length",
    )
    // `s.substring(start)` is encoded as a let that binds `s`
    val v = ValDef(FreshIdentifier("v"), StringType())
    check(Let(v, s, SubString(v.toVariable, IntegerLiteral(1), StringLength(v.toVariable))), "s.substring(1)")
  }

  test("Sets, bags and maps") {
    checkAll(
      FiniteSet(Seq(IntegerLiteral(1), IntegerLiteral(2)), IntegerType()) -> "Set(1, 2)",
      FiniteSet(Seq(), IntegerType()) -> "Set()",
      FiniteBag(Seq(IntegerLiteral(1) -> IntegerLiteral(3)), IntegerType()) -> "Bag(1 -> 3)",
      FiniteMap(Seq(), BooleanLiteral(false), IntegerType(), BooleanType()) -> "{* -> false}",
      FiniteMap(Seq(IntegerLiteral(1) -> BooleanLiteral(true), IntegerLiteral(2) -> BooleanLiteral(true)),
        BooleanLiteral(false), IntegerType(), BooleanType()) -> "{1 -> true, 2 -> true, * -> false}",
      ElementOfSet(x, set) -> "set.contains(x)",
      Not(ElementOfSet(x, set)) -> "!set.contains(x)",
      SubsetOf(set, set2) -> "set.subsetOf(set2)",
      Not(SubsetOf(set, set2)) -> "!set.subsetOf(set2)",
      SetAdd(set, x) -> "set + x",
      SetUnion(set, set2) -> "set ++ set2",
      SetDifference(set, set2) -> "set -- set2",
      SetIntersection(set, set2) -> "set & set2",
      BagAdd(bag, x) -> "bag + x",
      BagUnion(bag, bag2) -> "bag ++ bag2",
      BagDifference(bag, bag2) -> "bag -- bag2",
      BagIntersection(bag, bag2) -> "bag & bag2",
      MultiplicityInBag(x, bag) -> "bag(x)",
      MapApply(map, x) -> "map(x)",
      MapUpdated(map, x, p) -> "map.updated(x, p)",
      MapMerge(mask, map, map2) -> "mask.mapMerge(map, map2)",
      SetIntersection(SetUnion(set, set2), set) -> "set ++ set2 & set",
      SetUnion(set, SetIntersection(set2, set)) -> "set ++ (set2 & set)",
      SetDifference(set, SetUnion(set2, set)) -> "set -- (set2 ++ set)",
      SetUnion(SetAdd(set, x), set2) -> "(set + x) ++ set2",
      BagIntersection(BagUnion(bag, bag2), bag) -> "bag ++ bag2 & bag",
      And(ElementOfSet(x, set), SubsetOf(set, set2)) -> "set.contains(x) && set.subsetOf(set2)",
    )
  }

  test("Tuples, ADTs and functions") {
    val l = Variable(FreshIdentifier("l"), ADTType(listID, Seq(IntegerType())), Seq.empty)
    val fun = Variable(FreshIdentifier("fun"), FunctionType(Seq(IntegerType(), IntegerType()), IntegerType()), Seq.empty)
    val t = Variable(FreshIdentifier("t"), TupleType(Seq(IntegerType(), BooleanType())), Seq.empty)
    checkAll(
      Tuple(Seq(x, p)) -> "(x, p)",
      TupleSelect(t, 2) -> "t._2",
      ADT(nilID, Seq(IntegerType()), Seq()) -> "Nil[BigInt]()",
      ADT(consID, Seq(IntegerType()), Seq(x, l)) -> "Cons[BigInt](x, l)",
      IsConstructor(l, consID) -> "l is Cons",
      ADTSelector(l, headID) -> "l.head",
      FunctionInvocation(sizeID, Seq(IntegerType()), Seq(l)) -> "size[BigInt](l)",
      FunctionInvocation(constID, Seq(), Seq()) -> "const",
      Application(fun, Seq(x, y)) -> "fun(x, y)",
      Lambda(Seq(x.toVal, y.toVal), Plus(x, y)) -> "(x: BigInt, y: BigInt) => x + y",
      // eta-expanded functions are printed as the function name
      Lambda(Seq(l.toVal), FunctionInvocation(sizeID, Seq(), Seq(l))) -> "size",
      Application(Lambda(Seq(x.toVal), x), Seq(y)) -> "((x: BigInt) => x)(y)",
    )
  }

  test("Binders and control flow") {
    checkAll(
      Let(x.toVal, IntegerLiteral(1), Plus(x, x)) -> "val x: BigInt = 1\nx + x",
      Forall(Seq(x.toVal, y.toVal), Equals(x, y)) -> "forall((x: BigInt, y: BigInt) => (x == y))",
      Choose(x.toVal, GreaterThan(x, y)) -> "choose((x: BigInt) => x > y)",
      Assume(p, x) -> "assume(p)\nx",
      IfExpr(p, x, y) -> "if (p) {\n  x\n} else {\n  y\n}",
      IfExpr(p, x, IfExpr(q, y, z)) -> "if (p) {\n  x\n} else if (q) {\n  y\n} else {\n  z\n}",
      Plus(IfExpr(p, x, y), z) -> "(if (p) {\n  x\n} else {\n  y\n}) + z",
      // lets nested in other expressions are wrapped in braces
      Plus(Let(x.toVal, y, x), z) -> "{\n  val x: BigInt = y\n  x\n} + z",
      IfExpr(p, Let(x.toVal, y, x), z) -> "if (p) {\n  val x: BigInt = y\n  x\n} else {\n  z\n}",
    )
  }

  test("Value and type parameter definitions") {
    checkAll(
      x.toVal -> "x: BigInt",
      ValDef(FreshIdentifier("v"), IntegerType(), Seq(Annotation("ghost", Seq.empty))) -> "(v: BigInt) @ghost",
      TypeParameterDef(T) -> "T",
      TypeParameter(FreshIdentifier("U"), Seq(Annotation("mutable", Seq.empty))) -> "U @mutable",
    )
  }

  test("Types") {
    val vd = ValDef(FreshIdentifier("n"), IntegerType())
    checkAll(
      Untyped -> "<untyped>",
      UnitType() -> "Unit",
      Int8Type() -> "Byte",
      Int16Type() -> "Short",
      Int32Type() -> "Int",
      Int64Type() -> "Long",
      BVType(true, 12) -> "Int12",
      BVType(false, 12) -> "UInt12",
      IntegerType() -> "BigInt",
      RealType() -> "Real",
      CharType() -> "Char",
      BooleanType() -> "Boolean",
      StringType() -> "String",
      Float32Type() -> "Float",
      Float64Type() -> "Double",
      FPType(5, 11) -> "Float16",
      RoundingMode -> "RoundingMode",
      SetType(IntegerType()) -> "Set[BigInt]",
      BagType(IntegerType()) -> "Bag[BigInt]",
      MapType(IntegerType(), BooleanType()) -> "Map[BigInt, Boolean]",
      TupleType(Seq(IntegerType(), BooleanType())) -> "(BigInt, Boolean)",
      FunctionType(Seq(IntegerType(), BooleanType()), IntegerType()) -> "(BigInt, Boolean) => BigInt",
      ADTType(listID, Seq(IntegerType())) -> "List[BigInt]",
      ADTType(listID, Seq()) -> "List",
      RefinementType(vd, GreaterThan(vd.toVariable, IntegerLiteral(0))) -> "{ n: BigInt | (n > 0) }",
      PiType(Seq(vd), RefinementType(ValDef(FreshIdentifier("r"), IntegerType()), Equals(vd.toVariable, vd.toVariable))) ->
        "(n: BigInt) => { r: BigInt | (n == n) }",
      SigmaType(Seq(vd), IntegerType()) -> "(n: BigInt, BigInt)",
    )
  }

  test("Definitions") {
    check(listSort,
      s"""|@invariant(inv)
          |abstract class List[A]
          |case class Cons[A](head: A, tail: List[A]) extends List[A]
          |case class Nil[A]() extends List[A]""".stripMargin)

    check(listSort.constructors.head,
      "case class Cons(head: A, tail: List[A])[A] extends List[A]",
      PrinterOptions(symbols = Some(symbols)))
    // Without symbols, the sort's type parameters are unknown
    check(listSort.constructors.head, "case class Cons(head: A, tail: List[A]) extends List")

    check(sizeFd,
      s"""|@library
          |def size[A](l: List[A]): BigInt = if (l is Cons) {
          |  1 + size[A](l.tail)
          |} else {
          |  0
          |}""".stripMargin)

    check(constFd, "def const: BigInt = 42")
  }

  test("Typed definitions") {
    given Symbols = symbols
    checkAll(
      sizeFd.typed(Seq(IntegerType())) -> "typed def size[BigInt]",
      listSort.typed(Seq(IntegerType())) -> "typed class List[BigInt]",
      listSort.constructors.head.typed(Seq(IntegerType())) -> "typed class Cons[BigInt]",
    )
  }

  test("Unique identifiers") {
    val opts = PrinterOptions(printUniqueIds = true)
    check(x, x.id.uniqueName, opts)
    assert(x.id.uniqueName != "x")
  }

  test("Types of expressions") {
    val opts = PrinterOptions(printTypes = true, symbols = Some(symbols))
    check(Plus(x, IntegerLiteral(1)), "⟨⟨x : BigInt ⟩ + ⟨1 : BigInt ⟩ : BigInt ⟩", opts)
    // types can't be printed without symbols
    assertThrows[IllegalArgumentException](PrinterOptions(printTypes = true))
  }

  test("Positions") {
    val opts = PrinterOptions(printPositions = true)
    val file = new java.io.File("Test.scala")
    val e1 = IntegerLiteral(1).setPos(OffsetPosition(3, 4, 10, file))
    check(e1, "1@(3:4)", opts)
    val e2 = IntegerLiteral(2).setPos(RangePosition(3, 4, 10, 3, 4, 10, file))
    check(e2, "2@(3:4)", opts)
    val e3 = IntegerLiteral(3).setPos(RangePosition(3, 4, 10, 3, 8, 14, file))
    check(e3, "3@(3:4-8)", opts)
    val e4 = IntegerLiteral(4).setPos(RangePosition(3, 4, 10, 5, 8, 30, file))
    check(e4, "4@(3:4-5:8)", opts)
    check(IntegerLiteral(5), "5@(?)", opts)
  }

  test("Base indentation") {
    check(IfExpr(p, x, y), "if (p) {\n    x\n  } else {\n    y\n  }", PrinterOptions(baseIndent = 1))
  }

  test("Printing from a context") {
    val ctx = TestContext(Options(Seq(optPrintUniqueIds(true), optPrintUnicode(true), optPrintTypes(true))))
    val opts = PrinterOptions.fromContext(ctx)
    assert(opts.printUniqueIds && opts.printUnicode)
    // types are only printed when symbols are available
    assert(!opts.printTypes)
    assert(PrinterOptions.fromSymbols(symbols, ctx).printTypes)
  }

  test("asString") {
    given PrinterOptions = PrinterOptions()
    assert(asString(Plus(x, y)) == "x + y")
    assert(asString(x.id) == "x")
    assert(asString(42) == "42")
    assert(HasADTInvariant(invID).asString == "invariant(inv)")
    assert(Annotation("extern", Seq.empty).asString == "extern")
  }
}
