/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package tip

import org.scalatest.funsuite.AnyFunSuite

import java.io.StringReader
import scala.collection.immutable.BitSet

class ValuePrinterSuite extends AnyFunSuite {
  import inox.trees._

  private val header =
    """(declare-datatypes () ((Lst (nil) (cons (hd Int) (tl Lst)))))
      |(declare-datatypes (T) ((Opt (none) (some (get T)))))
      |(declare-sort U 0)
      |(declare-const l Lst)
      |(declare-const o (Opt Int))
      |(declare-const u U)
      |(declare-const f (=> Int Int))
      |(declare-const b (_ BitVec 8))
      |(declare-const s String)
      |(declare-const r Real)
      |(declare-const m (Array Int Bool))
      |(declare-const st (Set Int))
      |(declare-const bg (Bag Int))
      |""".stripMargin

  /** Parses `header` plus one assertion and returns the program and assertion. */
  private def parse(assertion: String): (InoxProgram, Expr) = {
    val script = header + s"(assert $assertion)\n(check-sat)\n"
    Parser(new StringReader(script)).parseScript.head
  }

  /** The value `v` that the input binds to `name` in `(= name v)`. */
  private def parseValue(name: String, value: String): (InoxProgram, Expr) = {
    val (program, expr) = parse(s"(= $name $value)")
    val Equals(_, v) = expr: @unchecked
    (program, v)
  }

  /** Checks that `value` prints as `expected` and that the printed term parses back to a
    * value that prints the same way (modulo the names of bound variables). */
  private def roundTrip(name: String, value: String, expected: String): Unit = {
    val (program, v) = parseValue(name, value)
    import program.symbols.given
    def strip(s: String) = s.replaceAll("\\$[0-9]+", "")
    val printed = ValuePrinter.value(v)
    assert(strip(printed) == strip(expected))
    val (program2, v2) = parseValue(name, printed)
    val reprinted = ValuePrinter.value(v2)(using program2.symbols)
    assert(strip(reprinted) == strip(printed))
  }

  test("integers, reals and booleans") {
    roundTrip("l", "(cons (- 3) (cons 4 nil))", "(cons (- 3) (cons 4 nil))")
    roundTrip("r", "(/ 1 3)", "(/ 1 3)")
    val (program, _) = parse("true")
    import program.symbols.given
    assert(ValuePrinter.value(FractionLiteral(-1, 3)) == "(/ (- 1) 3)")
    assert(ValuePrinter.value(BooleanLiteral(true)) == "true")
    assert(ValuePrinter.value(IntegerLiteral(-12)) == "(- 12)")
  }

  test("functions") {
    val (program, v) = parseValue("f", "(lambda ((x Int)) (ite (= x 2) 5 0))")
    val Lambda(Seq(x), _) = v: @unchecked
    val name = x.id.uniqueName
    assert(ValuePrinter.value(v)(using program.symbols) == s"(lambda (($name Int)) (ite (= $name 2) 5 0))")
    roundTrip("f", "(lambda ((x Int)) (ite (= x 2) 5 0))", ValuePrinter.value(v)(using program.symbols)
      .replace(name, "x$0"))
  }

  test("bit-vectors and characters") {
    roundTrip("b", "#b00000101", "#b00000101")
    val (program, _) = parse("true")
    import program.symbols.given
    assert(ValuePrinter.value(CharLiteral('A')) == "#b0000000001000001")
    assert(ValuePrinter.value(BVLiteral(true, BigInt(-1), 4)) == "#b1111")
  }

  test("strings, with SMT-LIB escapes") {
    roundTrip("s", "\"a\"\"b\"", "\"a\"\"b\"")
    val (program, _) = parse("true")
    import program.symbols.given
    assert(ValuePrinter.value(StringLiteral("é\\")) == "\"\\u{e9}\\u{5c}\"")
  }

  test("nullary constructors of parametric datatypes are qualified by their sort") {
    roundTrip("o", "(as none (Opt Int))", "(as none (Opt Int))")
    roundTrip("o", "(some 3)", "(some 3)")
    roundTrip("l", "nil", "nil")
  }

  test("values of uninterpreted sorts") {
    roundTrip("u", "(U 2)", "(U 2)")
  }

  test("maps as arrays") {
    val (program, _) = parse("true")
    import program.symbols.given
    val map = FiniteMap(Seq(IntegerLiteral(1) -> BooleanLiteral(true)), BooleanLiteral(false), IntegerType(), BooleanType())
    val printed = ValuePrinter.value(map)
    assert(printed == "(store ((as const (Array Int Bool)) false) 1 true)")
    val (_, v) = parseValue("m", printed)
    assert(v == MapUpdated(FiniteMap(Seq(), BooleanLiteral(false), IntegerType(), BooleanType()), IntegerLiteral(1), BooleanLiteral(true)))
  }

  test("sets and bags") {
    val (program, _) = parse("true")
    import program.symbols.given
    val set = FiniteSet(Seq(IntegerLiteral(1), IntegerLiteral(2)), IntegerType())
    val printedSet = ValuePrinter.value(set)
    assert(printedSet == "(insert (as emptyset Int) 1 2)")
    assert(parseValue("st", printedSet)._2.getType(using program.symbols) == SetType(IntegerType()))
    assert(ValuePrinter.value(FiniteSet(Seq(), IntegerType())) == "(as emptyset Int)")

    val bag = FiniteBag(Seq(IntegerLiteral(1) -> IntegerLiteral(3)), IntegerType())
    val printedBag = ValuePrinter.value(bag)
    assert(parseValue("bg", printedBag)._2.getType(using program.symbols) == BagType(IntegerType()))
  }

  test("abstract values of type parameters") {
    val (program, _) = parse("true")
    import program.symbols.given
    assert(ValuePrinter.value(GenericValue(TypeParameter.fresh("T"), 0)) == "@T_0")
  }

  test("models print as get-value responses sorted by name") {
    val (program, expr) = parse("(= l nil)")
    import program.symbols.given
    val Equals(lv: Variable, nil) = expr: @unchecked
    val fv = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    val x = ValDef.fresh("x", IntegerType())
    val model = Map(lv.toVal -> nil, fv.toVal -> Lambda(Seq(x), IntegerLiteral(7)))
    assert(ValuePrinter.model(model) == s"((f (lambda ((${x.id.uniqueName} Int)) 7)) (l nil))")
  }
}
