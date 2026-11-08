/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import Feature._

/** String operations and string models on every solver. */
class StringSemanticsSuite extends SolverTestSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses.{given, _}

  given Symbols = symbols

  /** The literal of the code points of `s`, where each surrogate pair is a single character. */
  def codePoints(s: String): StringLiteral = StringLiteral(s.codePoints.toArray.toSeq)

  // Strings containing special characters: control characters, multi-byte UTF-8 characters,
  // characters outside of the BMP, surrogates and character sequences that look like escape sequences.
  // As in SMT-LIB, each code point is a character: `codePoints("😀")` is a single one.
  val specialStrings = Seq("abc", "\n", "\u0000x", "é", "€", "😀", "\ud83d", "ÿĀ", "\uffff", "\ud800", "\\u{41}", "\\x41", "\\", "a\"b")

  // One test per string, so that they run in parallel
  for (str <- specialStrings) {
    val shown = str.flatMap(c => if (c >= ' ' && c < '\u007f') c.toString else f"\\u${c.toInt}%04x")
    test(s"String Operations on \"$shown\"", Strings) { ctx =>
      val s = solver(ctx)
      val lit = codePoints(str)
      val cps = lit.value
      val xy = StringLiteral("xy")
      check(s, lit, lit)
      check(s, StringLength(lit), IntegerLiteral(cps.length))
      check(s, StringConcat(lit, xy), StringLiteral(cps ++ xy.value))
      check(s, SubString(StringConcat(xy, lit), IntegerLiteral(1), IntegerLiteral(3)), StringLiteral((xy.value ++ cps).slice(1, 3)))

      // make sure lengths are also correct for non-ground strings
      val v = Variable.fresh("v", StringType())
      assert(s.solveVALID(Implies(Equals(v, lit), Equals(StringLength(v), IntegerLiteral(cps.length)))) contains true)
    }
  }

  test("Surrogates are characters of their own", Strings) { ctx =>
    val s = solver(ctx)
    // the UTF-16 code units of "😀", which are two characters, unlike its code point
    val units = StringLiteral("😀")
    assert(units == StringLiteral(Seq(0xD83D, 0xDE00)))
    check(s, StringLength(units), IntegerLiteral(2))
    check(s, StringLength(codePoints("😀")), IntegerLiteral(1))
    check(s, Equals(units, codePoints("😀")), BooleanLiteral(false))
    // concatenating a high and a low surrogate doesn't make a single character
    check(s, StringLength(StringConcat(StringLiteral(Seq(0xD83D)), StringLiteral(Seq(0xDE00)))), IntegerLiteral(2))
    assert(StringLiteral.fromUTF8("a😀".getBytes("UTF-8")) == StringLiteral(Seq('a'.toInt, 0x1F600)))
    check(s, SubString(codePoints("a😀b"), IntegerLiteral(1), IntegerLiteral(2)), codePoints("😀"))
  }

  test("String Models outside of the BMP", Strings) { ctx =>
    val s = solver(ctx)
    val v = Variable.fresh("v", StringType())
    for (c <- Seq(0x10000, 0x1F600, StringLiteral.MaxCodePoint)) {
      val clause = Equals(v, StringConcat(StringLiteral(Seq(c)), StringLiteral("a")))
      s.solveSAT(clause) match {
        case SatWithModel(model) => assert(model.vars(v.toVal) == StringLiteral(Seq(c, 'a'.toInt)))
        case got => fail(s"Solving of '$clause' failed with $got.")
      }
    }
  }

  test("String Models in the BMP with --strings-bmp", Strings) { ctx =>
    val s = solver(ctx.withOpts(optStringsBMP(true)))
    val v = Variable.fresh("v", StringType())
    for (len <- 1 to 2) {
      s.solveSAT(Equals(StringLength(v), IntegerLiteral(len))) match {
        case SatWithModel(model) =>
          val cps = model.vars(v.toVal).asInstanceOf[StringLiteral].value
          assert(cps.length == len && cps.forall(_ <= 0xFFFF), s"Invalid model $cps")
        case got => fail(s"Solving failed with $got.")
      }
    }
    check(s, StringLength(StringLiteral("a😀")), IntegerLiteral(3))
  }

  test("Native Z3 string alphabets in one thread", Strings) { ctx =>
    // Z3's alphabet is a global parameter: a thread can't use both alphabets at the same time
    if (Set("nativez3", "unrollz3").contains(ctx.options.findOptionOrDefault(optSelectedSolvers).head)) {
      val bmpCtx = ctx.withOpts(optStringsBMP(true))
      val full = program.getSolver(ctx).getNewSolver()
      try {
        program.getSolver(ctx).getNewSolver().free()
        assertThrows[z3.Z3Native.EncodingConflictException](program.getSolver(bmpCtx).getNewSolver())
      } finally {
        full.free()
      }
      program.getSolver(bmpCtx).getNewSolver().free()
    }
  }

  test("Substrings out of bounds", Strings) { ctx =>
    val s = solver(ctx)

    def sub(str: String, from: BigInt, to: BigInt) =
      SubString(codePoints(str), IntegerLiteral(from), IntegerLiteral(to))

    check(s, sub("abc", 1, 10), StringLiteral("bc"))
    check(s, sub("abc", -1, 2), StringLiteral(""))
    check(s, sub("abc", 3, 4),  StringLiteral(""))
    check(s, sub("abc", 2, 1),  StringLiteral(""))
    check(s, sub("😀😀", 1, 2), codePoints("😀"))
  }

  test("String Models", Strings) { ctx =>
    val s = solver(ctx)

    // the extracted models must satisfy the constraints (in particular after decoding)
    val v = Variable.fresh("v", StringType())
    for (len <- 1 to 3) {
      val clause = And(Equals(StringLength(v), IntegerLiteral(len)), Not(Equals(v, StringLiteral("a" * len))))
      s.solveSAT(clause) match {
        case SatWithModel(model) =>
          val str = model.vars(v.toVal).asInstanceOf[StringLiteral].value
          assert(str.length == len && str != Seq.fill(len)('a'.toInt), s"Invalid model $str")
        case got => fail(s"Solving of '$clause' failed with $got.")
      }
    }
  }

  test("String Models with non-ASCII characters", Strings) { ctx =>
    val s = solver(ctx)

    // force the solver to pick a character outside of the (extended) ASCII range,
    // which must be decoded to a valid Inox character
    val v = Variable.fresh("v", StringType())
    val clause = andJoin(Equals(StringLength(v), IntegerLiteral(1)) +:
      (0 to 0xFF).map(c => Not(Equals(v, StringLiteral(c.toChar.toString)))))
    s.solveSAT(clause) match {
      case SatWithModel(model) =>
        val str = model.vars(v.toVal).asInstanceOf[StringLiteral].value
        assert(str.length == 1 && str.head > 0xFF, s"Invalid model $str")
      case got => fail(s"Solving of '$clause' failed with $got.")
    }
  }

  test("Empty and non-empty string models", Strings) { ctx =>
    val s = solver(ctx)
    val v = Variable.fresh("v", StringType())

    assert(s.solveSAT(Equals(v, StringLiteral(""))).isSAT)
    assert(s.solveSAT(Not(Equals(v, StringLiteral("")))).isSAT)
    assert(s.solveSAT(GreaterThan(StringLength(v), IntegerLiteral(0))).isSAT)
  }

  test("Ground string (dis-)equality", Strings) { ctx =>
    val s = solver(ctx)

    assert(s.solveSAT(Equals(StringLiteral(""), StringLiteral(""))).isSAT)
    assert(s.solveSAT(Not(Equals(StringLiteral(""), StringLiteral("")))).isUNSAT)
  }

  test("Non-ASCII strings", Strings) { ctx =>
    val s = solver(ctx)

    check(s, StringLiteral("abéà"), StringLiteral("abéà"))
    check(s, StringLength(StringLiteral("abéà")), IntegerLiteral(4))
  }
}
