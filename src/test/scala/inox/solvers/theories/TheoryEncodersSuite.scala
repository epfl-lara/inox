/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package theories

import org.scalatest.funsuite.AnyFunSuite

/** Checks the theory encoders without any SMT solver: the theory encoders produce programs
  * that the Inox evaluator can run, so evaluating an encoded expression in the encoded program
  * and decoding the result must give the same value as evaluating the original expression.
  */
class TheoryEncodersSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}

  given symbols: Symbols = NoSymbols
  val program = InoxProgram(symbols)
  val ctx = TestContext.empty
  given PrinterOptions = PrinterOptions(symbols = Some(symbols))

  type Encoder = transformers.ProgramTransformer {
    val sourceProgram: Program { val trees: inox.trees.type }
    val targetProgram: Program { val trees: inox.trees.type }
  }

  private def evalIn(p: Program { val trees: inox.trees.type }, e: Expr): Expr =
    p.getEvaluator(ctx).eval(e) match {
      case evaluators.EvaluationResults.Successful(v) => v
      case res => fail(s"Evaluation of ${e.asString} failed with $res")
    }

  /** Checks that `decode(eval(encode(e)))` and `eval(e)` coincide. */
  protected def checkEncoding(enc: Encoder, e: Expr): Unit = {
    val expected = evalIn(enc.sourceProgram, e)
    val encoded = enc.encode(e.asInstanceOf[enc.sourceProgram.trees.Expr])
    val result = evalIn(enc.targetProgram, encoded.asInstanceOf[Expr])
    // evaluating the decoded result normalizes it (e.g. finite sets, bags and fractions)
    val decoded = evalIn(enc.sourceProgram, enc.decode(result.asInstanceOf[enc.targetProgram.trees.Expr]).asInstanceOf[Expr])
    assert(decoded == expected,
      s"\n  expression: ${e.asString}\n  encoded:    ${encoded.asInstanceOf[Expr].asString}\n  expected:   ${expected.asString}\n  got:        ${decoded.asString}")
  }

  protected def checkAll(enc: Encoder, es: Seq[Expr]): Unit = es.foreach(checkEncoding(enc, _))

  // Strings with special characters: control characters, two- and three-byte UTF-8
  // characters, surrogate pairs and sequences that look like SMT-LIB/Java escapes.
  val strings = Seq("", "abc", "\n", "\u0000x", "é", "abéà", "€", "😀", "ÿĀ",
    "\\u{41}", "\\x41", "\\", "a\"b")

  def stringExprs: Seq[Expr] = strings.flatMap { s =>
    val lit = StringLiteral(s)
    Seq(
      lit,
      StringLength(lit),
      StringConcat(lit, StringLiteral("xy")),
      StringConcat(StringLiteral("\t"), lit),
      StringLength(StringConcat(lit, lit)),
      SubString(StringConcat(lit, StringLiteral("xyz")), IntegerLiteral(1), IntegerLiteral(3)),
      SubString(StringConcat(StringLiteral("xyz"), lit), IntegerLiteral(1), Plus(IntegerLiteral(1), IntegerLiteral(2))),
      Equals(lit, StringLiteral("abc")),
    )
  }

  test("String encoder") {
    checkAll(StringEncoder(program), stringExprs)
  }

  def bagExprs: Seq[Expr] = {
    val tpe = IntegerType()
    def i(n: Int) = IntegerLiteral(n)
    val empty = FiniteBag(Seq.empty, tpe)
    val bags = Seq(
      empty,
      BagAdd(BagAdd(empty, i(1)), i(1)), // key 1 occurs twice in the encoding
      FiniteBag(Seq(i(1) -> i(1), i(2) -> i(3)), tpe),
      FiniteBag(Seq(i(1) -> i(5), i(1) -> i(2)), tpe), // the last value of a key wins
      FiniteBag(Seq(i(2) -> i(0), i(1) -> i(-1), i(3) -> i(1)), tpe), // non-positive multiplicities are dropped
      BagUnion(BagAdd(empty, i(2)), BagAdd(BagAdd(empty, i(1)), i(2))),
    )

    val ops = for (b1 <- bags; b2 <- bags; op <- Seq(BagUnion.apply, BagDifference.apply, BagIntersection.apply)) yield op(b1, b2)
    val all = bags ++ bags.map(BagAdd(_, i(3))) ++ ops
    all ++ all.flatMap(b => Seq(1, 2, 3).map(k => MultiplicityInBag(i(k), b)))
  }

  test("Bag encoder") {
    val ev = program.getEvaluator(ctx)
    checkAll(BagEncoder(transformers.ProgramEncoder.empty(program))(ev).asInstanceOf[Encoder], bagExprs)
  }

  def setExprs: Seq[Expr] = {
    val tpe = IntegerType()
    def i(n: Int) = IntegerLiteral(n)
    val empty = FiniteSet(Seq.empty, tpe)
    val sets = Seq(
      empty,
      FiniteSet(Seq(i(1), i(1)), tpe),
      SetAdd(SetAdd(empty, i(2)), i(2)),
      FiniteSet(Seq(i(1), i(2), i(3)), tpe),
    )

    val ops = for (s1 <- sets; s2 <- sets; op <- Seq(SetUnion.apply, SetDifference.apply, SetIntersection.apply)) yield op(s1, s2)
    val all = sets ++ sets.map(SetAdd(_, i(3))) ++ ops
    all ++ all.flatMap(s => Seq(1, 2, 3).map(k => ElementOfSet(i(k), s)))
  }

  test("Set encoder") {
    checkAll(SetEncoder(program), setExprs)
  }

  def realExprs: Seq[Expr] = {
    val values = Seq(
      FractionLiteral(1, 2),
      FractionLiteral(-1, 3),
      FractionLiteral(2, 4), // not normalized
      FractionLiteral(1, -2), // negative denominator
      FractionLiteral(0, 1),
    )
    val arith = for (a <- values; b <- values; op <- Seq(Plus.apply, Minus.apply, Times.apply)) yield op(a, b)
    val divs = for (a <- values; b <- values if b != FractionLiteral(0, 1)) yield Division(a, b)
    val all = values ++ values.map(UMinus(_)) ++ arith ++ divs
    val zero = FractionLiteral(0, 1)
    val comparisons = for {
      a <- all
      b <- Seq(zero, FractionLiteral(1, 4))
      op <- Seq(LessThan.apply, LessEquals.apply, GreaterThan.apply, GreaterEquals.apply)
    } yield op(a, b)
    all ++ comparisons
  }

  test("Real encoder") {
    checkAll(RealEncoder(program), realExprs)
  }

  test("SMT-LIB string escapes round-trip") {
    import utils.StringUtils._
    for (s <- strings ++ Seq("\u007f", "￿", "\ud800")) {
      val enc = encode(s)
      assert(enc.forall(c => c >= 0x20 && c <= 0x7E), s"encoding of ${s.toList.map(_.toInt)} is not printable ASCII: $enc")
      assert(decode(enc) == s, s"round-trip failed for ${s.toList.map(_.toInt)}: $enc")
    }

    // SMT-LIB 2.6 escape sequences as printed by solvers
    assert(decode("\\u{41}\\u{0}\\u{e9}\\u{20ac}\\u{1f600}") == "A\u0000é€😀")
    assert(decode("\\u0041\\u20ac") == "A€")
    // backslashes that do not start an escape sequence are kept as-is
    assert(decode("\\x41\\n\\u{}\\u{123456}\\u12") == "\\x41\\n\\u{}\\u{123456}\\u12")

    // model strings must map SMT-LIB characters one-to-one to Inox characters
    assert(decodeBMP("\\u{41}\\u{ffff}\\u{d800}") == Some("A\uffff\ud800"))
    assert(decodeBMP("a\\u{10000}") == None)
    assert(decodeBMP("a\\u{1f600}b") == None)
    assert(decodeBMP("a😀") == None)
    for (s <- strings) assert(decodeBMP(encode(s)) == Some(s))
  }
}
