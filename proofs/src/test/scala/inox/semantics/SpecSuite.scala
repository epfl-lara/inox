/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package semantics

import java.nio.file.{Files, Path}

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

  /** Writes each `(name, text)` to a fresh directory, and loads the first. */
  private def load(files: (String, String)*): Spec = {
    val dir = Files.createTempDirectory("spec")
    for ((n, t) <- files) Files.writeString(dir.resolve(n), t)
    Spec.load(dir.resolve(files.head._1))
  }

  test("A file extends the datatypes and functions of the files it imports") {
    val base = file(result, "(datatype E (Lit (v Int)))\n(define (eval (e E)) (Result Int) :cases e)",
      "(case eval (Lit v) (Ok v))")
    val ext = file("(import \"base.md\")", "(extend-datatype Result (Fail) (Throw (v Int)))",
      "(extend-datatype E (Neg (e E)) (Abort))",
      "(case eval (Neg e) (let! ((v (eval e))) (Ok (- 0 v))))", "(case eval (Abort) (Fail))")
    val spec = load("ext.md" -> ext, "base.md" -> base)
    assert(spec.datatypes.find(_.name == "E").get.ctors.map(_.name) == Seq("Lit", "Neg", "Abort"))
    assert(spec.datatypes.find(_.name == "Result").get.ctors.map(_.name) == Seq("Ok", "Stuck", "OutOfFuel", "Fail", "Throw"))
    // `let!` propagates the new outcome
    val scala = ScalaBackend(spec, "ext.md", "p")
    assert(scala.contains("case Fail() => Fail()") && scala.contains("case r: Throw => r"), scala)

    val missing = file("(import \"base.md\")", "(extend-datatype E (Neg (e E)))")
    val e = intercept[Spec.SpecError](load("ext.md" -> missing, "base.md" -> base))
    assert(e.getMessage.contains("eval has no case for Neg"), e.getMessage)
  }

  test("Imports are read once, and only through Spec.load") {
    val base = file(result)
    val mid = file("(import \"base.md\")", "(datatype B (T))")
    val top = file("(import \"mid.md\")", "(import \"base.md\")")
    assert(load("top.md" -> top, "mid.md" -> mid, "base.md" -> base).datatypes.map(_.name) == Seq("Result", "B"))
    rejects(top, "can't import others")
    val cyc = file("(import \"cyc.md\")")
    val e = intercept[Spec.SpecError](load("cyc.md" -> cyc))
    assert(e.getMessage.contains("imports itself"), e.getMessage)
  }

  test("Extensions name a declared datatype, and outcomes hold no result") {
    rejects(file(result, "(extend-datatype B (T))"), "extension of B, which isn't declared")
    rejects(file(result, "(extend-datatype Result (Partial (v T)))"), "other constructors don't hold a T")
  }
}
