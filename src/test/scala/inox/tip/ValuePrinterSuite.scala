/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package tip

import org.scalatest.funsuite.AnyFunSuite

import java.io.StringReader

class ValuePrinterSuite extends AnyFunSuite {
  import inox.trees._

  private val header =
    """(declare-datatypes () ((Lst (nil) (cons (hd Int) (tl Lst)))))
      |(declare-const l Lst)
      |(declare-const f (=> Int Int))
      |""".stripMargin

  /** Parses `header` plus one assertion and returns the program and assertion. */
  private def parse(assertion: String): (InoxProgram, Expr) = {
    val script = header + s"(assert $assertion)\n(check-sat)\n"
    Parser(new StringReader(script)).parseScript.head
  }

  test("integers, booleans and constructors print as SMT-LIB terms") {
    val (program, expr) = parse("(= l (cons (- 3) (cons 4 nil)))")
    val Equals(_, value) = expr: @unchecked
    assert(ValuePrinter.value(value) == "(cons (- 3) (cons 4 nil))")
    assert(ValuePrinter.value(BooleanLiteral(true)) == "true")
    assert(ValuePrinter.value(IntegerLiteral(-12)) == "(- 12)")
  }

  test("printed values parse back to the same value") {
    val (program, expr) = parse("(and (= l (cons 1 (cons (- 2) nil))) (= f (lambda ((x Int)) (ite (= x 2) 5 0))))")
    val And(Seq(Equals(_, lst), Equals(_, fun))) = expr: @unchecked
    for (v <- Seq(lst, fun)) {
      val printed = ValuePrinter.value(v)
      val target = if (v eq lst) "l" else "f"
      val (_, reparsed) = parse(s"(= $target $printed)")
      val Equals(_, v2) = reparsed: @unchecked
      // compare modulo the names of bound variables
      assert(ValuePrinter.value(v2).replaceAll("\\$[0-9]+", "") == printed.replaceAll("\\$[0-9]+", ""))
    }
  }

  test("models print as get-value responses sorted by name") {
    val (program, expr) = parse("(= l nil)")
    val Equals(lv: Variable, nil) = expr: @unchecked
    val fv = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    val x = ValDef.fresh("x", IntegerType())
    val model = Map(lv.toVal -> nil, fv.toVal -> Lambda(Seq(x), IntegerLiteral(7)))
    assert(ValuePrinter.model(model) == s"((f (lambda ((${x.id.uniqueName} Int)) 7)) (l nil))")
  }
}
