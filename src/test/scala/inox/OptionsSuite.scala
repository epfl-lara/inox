/* Copyright 2009-2026 EPFL, Lausanne */

package inox

import org.scalatest.funsuite.AnyFunSuite

import scala.concurrent.duration._

class OptionsSuite extends AnyFunSuite {
  import OptionParsers._
  import OptionsHelpers._

  given reporter: Reporter = new TestSilentReporter

  object optFlag extends FlagOptionDef("flag", false)
  object optMarker extends MarkerOptionDef("marker")
  object optString extends StringOptionDef("str", "default", "s")
  object optInt extends IntOptionDef("int", 3, "n")
  object optLong extends LongOptionDef("long", 4L, "n")
  object optDouble extends DoubleOptionDef("double", 0.5, "d")
  object optInts extends SeqOptionDef[Int] {
    val name = "ints"
    val default = Seq(1, 2)
    val elementParser = intParser
    val usageRhs = "i1,i2,..."
  }
  object optNames extends SetOptionDef[String] {
    val name = "names"
    val default = Set.empty[String]
    val elementParser = stringParser
    val usageRhs = "n1,n2,..."
  }

  test("Base parsers accept well-formed values only") {
    assert(intParser("42") == Some(42) && intParser("4.2").isEmpty && intParser("").isEmpty)
    assert(longParser("12345678901") == Some(12345678901L) && longParser("x").isEmpty)
    assert(doubleParser("1.5") == Some(1.5) && doubleParser("one").isEmpty)
    assert(stringParser("") == Some(""))
  }

  test("Boolean parser accepts the usual spellings") {
    for (s <- Seq("on", "true", "yes", "")) assert(booleanParser(s) == Some(true), s)
    for (s <- Seq("off", "false", "no")) assert(booleanParser(s) == Some(false), s)
    assert(booleanParser("maybe").isEmpty)
  }

  test("Sequence and set parsers split on commas") {
    assert(seqParser(intParser)("1,2,3") == Some(Seq(1, 2, 3)))
    assert(seqParser(intParser)("1,,2,") == Some(Seq(1, 2)))
    assert(seqParser(intParser)("") == Some(Seq()))
    assert(seqParser(intParser)("1,x,3").isEmpty)
    assert(seqParser(intParser)("1,2,x").isEmpty)
    assert(setParser(intParser)("3,1,3") == Some(Set(1, 3)))
  }

  test("Command line arguments are split into name and value") {
    assert(nameValue("--timeout=3") == Some(("timeout", "3")))
    assert(nameValue("--solvers=a,b=c") == Some(("solvers", "a,b=c")))
    assert(nameValue("--debug") == Some(("debug", "")))
    assert(nameValue("--x=") == Some(("x", "")))
    assert(nameValue("file.scala").isEmpty)
    assert(nameValue("-x").isEmpty)
  }

  test("Name patterns support wildcards and qualified suffixes") {
    val m = matcher(Seq("size"))
    assert(m("size") && m("List.size") && m("a.b.size"))
    assert(!m("thesize") && !m("sizes") && !m("size.x"))

    val prefix = matcher(Seq("List._"))
    assert(prefix("List.size") && prefix("x.List.map") && !prefix("Lists.size"))

    val infix = matcher(Seq("get_Or"))
    assert(infix("getOr") && infix("getAndOr") && infix("Option.getOrElse") == false)

    val suffix = matcher(Seq("_Else"))
    assert(suffix("getOrElse") && suffix("Option.orElse") && suffix("Else") && !suffix("Elsewhere"))

    val special = matcher(Seq("a+b"))
    assert(special("a+b") && !special("aab"))

    val several = matcher(Seq("foo", "bar"))
    assert(several("foo") && several("X.bar") && !several("baz"))
    assert(!matcher(Seq())("anything"))
  }

  test("Inclusion filters take precedence over exclusion filters") {
    val even = (i: Int) => i % 2 == 0
    val small = (i: Int) => i < 3
    assert((1 to 5).filter(filterInclusive(Some(even), Some(small))) == Seq(2, 4))
    assert((1 to 5).filter(filterInclusive(None, Some(small))) == Seq(3, 4, 5))
    assert((1 to 5).filter(filterInclusive[Int](None, None)) == (1 to 5))
  }

  test("Option definitions parse their values") {
    assert(optFlag.parse("").value == true)
    assert(optFlag.parse("off").value == false)
    assert(optMarker.parse("").value == true)
    assert(optString.parse("hello").value == "hello")
    assert(optInt.parse("7").value == 7)
    assert(optLong.parse("8").value == 8L)
    assert(optDouble.parse("2.5").value == 2.5)
    assert(optInts.parse("4,5").value == Seq(4, 5))
    assert(optNames.parse("a,b,a").value == Set("a", "b"))
    assert(optTimeout.parse("1.5").value == 1.5.seconds)
  }

  test("Invalid option values are fatal errors") {
    val e = intercept[FatalError](optInt.parse("seven"))
    assert(e.msg.contains("Invalid option usage: --int=seven"))
    assertThrows[FatalError](optMarker.parse("true"))
    assertThrows[FatalError](optFlag.parse("maybe"))
    assertThrows[FatalError](optTimeout.parse("soon"))
  }

  test("Resource limits are converted from millions without overflowing") {
    import solvers.smtlib.{optZ3Rlimit, optCVC5Rlimit}
    // Beyond Int: rejected instead of overflowing once multiplied by a million
    for (opt <- Seq(optZ3Rlimit, optCVC5Rlimit)) {
      assert(opt.parse("2147483647").value == Int.MaxValue)
      assertThrows[FatalError](opt.parse("10000000000000"))
    }
  }

  test("Usage strings show the expected argument") {
    assert(optFlag.usageDesc == "--flag[=true|false]")
    assert(optMarker.usageDesc == "--marker")
    assert(optInt.usageDesc == "--int=n")
    assert(optMarker.formatDefault == "")
    assert(optInt.formatDefault == "3")
    assert(optInts.formatDefault == "1,2")
    assert(optNames.formatDefault == "<none>")
  }

  test("Option values compare by option name and value") {
    assert(optInt(3) == optInt.withDefaultValue)
    assert(optInt(3) != optInt(4))
    assert(optInt(3).hashCode == optInt.withDefaultValue.hashCode)
    assert(optInt(3).toString == "--int=3")
    assert(optInt == IntOptionDef("int", 0, ""))
    assert(optInt != optLong)
  }

  test("Options look up values and fall back to defaults") {
    val opts = Options(Seq(optInt(5), optFlag(true)))
    assert(opts.findOption(optInt) == Some(5))
    assert(opts.findOption(optString).isEmpty)
    assert(opts.findOptionOrDefault(optString) == "default")
    assert(opts.findOptionOrDefault(optFlag))
    assert(Options.empty.findOptionOrDefault(optInt) == 3)
  }

  test("Adding options replaces earlier values of the same option") {
    val opts = Options(Seq(optInt(5), optFlag(true)))
    val updated = opts + optInt(6)
    assert(updated.findOption(optInt) == Some(6))
    assert(updated.options.size == 2)

    val merged = opts ++ Seq(optFlag(false), optString("s"))
    assert(merged.findOption(optFlag) == Some(false))
    assert(merged.findOption(optString) == Some("s"))
    assert(merged.findOption(optInt) == Some(5))
    assert(merged.options.size == 3)

    assert((opts ++ Options(Seq(optInt(1)))).findOption(optInt) == Some(1))
  }

  test("Only supported solvers can be selected") {
    assert(optSelectedSolvers.parse("smt-z3,princess").value == Set("smt-z3", "princess"))
    assert(optSelectedSolvers.parse("smt-z3:z3-4.8,no-inc:smt-cvc5").value == Set("smt-z3:z3-4.8", "no-inc:smt-cvc5"))
    assertThrows[FatalError](optSelectedSolvers.parse("smt-z3,unknown"))
    assertThrows[FatalError](optSelectedSolvers.parse("no-inc:princess"))
    assert(optSelectedSolvers.formatDefault == "nativez3")
  }
}
