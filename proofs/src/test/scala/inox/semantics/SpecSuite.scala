/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

import org.scalatest.funsuite.AnyFunSuite

/** The reader of semantics files rejects the blocks it doesn't understand. */
class SpecSuite extends AnyFunSuite {

  private val result = "(datatype (Result T) (Ok (value T)) (Stuck) (OutOfFuel))"

  private def file(blocks: String*): String =
    blocks.map(b => s"Some prose.\n\n```inox-sem\n$b\n```\n").mkString("\n")

  private def rejects(text: String, message: String): Unit = {
    val e = intercept[Spec.SpecError](Spec.parse(text))
    assert(e.getMessage.contains(message), e.getMessage)
  }

  test("Only the blocks tagged inox-sem count") {
    val spec = Spec.parse(file(result, "(datatype B (T) (F))") + "\n```\n(not a block)\n```\n")
    assert(spec.datatypes.map(_.name) == Seq("Result", "B"))
  }

  test("A function by cases needs one case per constructor, in any block") {
    val defs = "(datatype B (T) (F))\n(define (neg (b B)) B :cases b)\n(case neg (T) (F))"
    rejects(file(result, defs), "neg has no case for F")
    val spec = Spec.parse(file(result, defs, "(case neg (F) (T))"))
    assert(spec.functionsByName("neg").body.isInstanceOf[Spec.Body.Cases])
    rejects(file(result, defs, "(case neg (F) (T))", "(case neg (T) (T))"), "several cases for T")
  }

  test("Unknown names, wrong arities and unclosed blocks are errors") {
    rejects(file(result, "(define (f (x Int)) Int y)"), "unbound variable y")
    rejects(file(result, "(define (f (x Int)) Int (+ x))"), "+ takes 2 arguments")
    rejects(file(result, "(define (f (x Nat)) Int x)"), "unknown type Nat")
    rejects(file(result, "(datatype B (T) (F))", "(define (f (x Int)) B (T x))"), "constructor T has 0 fields")
    rejects("```inox-sem\n(datatype B (T))\n", "isn't closed")
    rejects(file("(datatype B (T))"), "must declare (datatype (Result T)")
  }
}
