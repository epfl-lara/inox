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

  // Strings containing special characters: control characters, multi-byte UTF-8 characters,
  // surrogate pairs and character sequences that look like escape sequences.
  val specialStrings = Seq("abc", "\n", "\u0000x", "é", "€", "😀", "\\u{41}", "\\x41", "\\", "a\"b")

  test("String Operations", Strings) { ctx =>
    val s = solver(ctx)

    for (str <- specialStrings) {
      val lit = StringLiteral(str)
      check(s, lit, lit)
      check(s, StringLength(lit), IntegerLiteral(str.length))
      check(s, StringConcat(lit, StringLiteral("xy")), StringLiteral(str + "xy"))
      check(s, SubString(StringConcat(StringLiteral("xy"), lit), IntegerLiteral(1), IntegerLiteral(3)), StringLiteral(("xy" + str).substring(1, 3)))

      // make sure lengths are also correct for non-ground strings
      val v = Variable.fresh("v", StringType())
      assert(s.solveVALID(Implies(Equals(v, lit), Equals(StringLength(v), IntegerLiteral(str.length)))) contains true)
    }
  }

  test("String Models", Strings) { ctx =>
    val s = solver(ctx)

    // the extracted models must satisfy the constraints (in particular after decoding)
    val v = Variable.fresh("v", StringType())
    for (len <- 1 to 3) {
      val clause = And(Equals(StringLength(v), IntegerLiteral(len)), Not(Equals(v, StringLiteral("a" * len))))
      s.solveSAT(clause) match {
        case SatWithModel(model) =>
          val StringLiteral(str) = model.vars(v.toVal): @unchecked
          assert(str.length == len && str != "a" * len, s"Invalid model ${str.toList.map(_.toInt)}")
        case got => fail(s"Solving of '$clause' failed with $got.")
      }
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
