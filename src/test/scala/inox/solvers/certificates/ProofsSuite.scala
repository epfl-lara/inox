/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package certificates

import org.scalatest.funsuite.AnyFunSuite

/** Proofs and certificates as data, without a solver. */
class ProofsSuite extends AnyFunSuite {
  import SolverResponses._

  def parsed(text: String): Seq[SExpr] = SExpr.parse(text) match {
    case Right(es) => es
    case Left(why) => fail(s"$text doesn't parse: $why")
  }

  def asserting(t: String) = SList(Seq(Atom("assert"), Atom(t)))

  test("S-expressions keep the text of their atoms") {
    val text = "(step @p1 :rule arith (-1 1/2 #b01 \"a \"\" ( b\" |x y|)) (@t1)"
    assert(parsed(text) == Seq(
      SList(Seq(Atom("step"), Atom("@p1"), Atom(":rule"), Atom("arith"),
        SList(Seq(Atom("-1"), Atom("1/2"), Atom("#b01"), Atom("\"a \"\" ( b\""), Atom("|x y|"))))),
      SList(Seq(Atom("@t1")))))
    assert(parsed(text).mkString(" ") == text)
  }

  test("S-expressions drop comments and whitespace") {
    assert(parsed("; a comment\n(a\n  b) ; another\n c") == Seq(SList(Seq(Atom("a"), Atom("b"))), Atom("c")))
    assert(parsed("(a) ; until the end") == Seq(SList(Seq(Atom("a")))))
    assert(parsed("") == Seq())
  }

  test("Unbalanced or unterminated s-expressions don't parse") {
    for (text <- Seq("(a", "a)", "|a", "\"a", "(a \"b\"\" c)")) assert(SExpr.parse(text).isLeft, text)
  }

  test("Resolving maps the session's symbols, quoted or not, and keeps their text") {
    val x = inox.trees.Variable.fresh("x", inox.trees.IntegerType())
    val table = Map("x!0" -> Ref.Variable(x))
    val resolved = parsed("(f x!0 |x!0| y)").map(_.resolve(table.get))
    assert(resolved == Seq(SList(Seq(Atom("f"), Sym("x!0", Ref.Variable(x)), Sym("|x!0|", Ref.Variable(x)), Atom("y")))))
    assert(resolved.mkString == "(f x!0 |x!0| y)")
    assert(resolved.map(_.resolve(_ => None)) == resolved)
  }

  test("A script proof has the asserts of its script and prints both blocks") {
    val proof = ScriptProof(Seq(SList(Seq(Atom("declare-const"), Atom("a"), Atom("Bool"))), asserting("a"), asserting("(not a)")),
      parsed("(assume @p1 a)"))
    assert(proof.asserts == Seq(Atom("a"), Atom("(not a)")))
    assert(proof.toString == "(script\n(declare-const a Bool)\n(assert a)\n(assert (not a))\n(check-sat)\n)\n(cpc\n(assume @p1 a)\n)")
  }

  test("Symbols are described by their kind, identifiers and types") {
    import inox.trees._
    val id = FreshIdentifier("f")
    val ft = FunctionType(Seq(IntegerType()), BooleanType())
    assert(Ref.Function(id, Seq(IntegerType())).describe == Seq("function", id.uniqueName, "BigInt"))
    assert(Ref.Uninterpreted(id).describe == Seq("uninterpreted", id.uniqueName))
    assert(Ref.Lambda(ft).describe == Seq("application", "(BigInt) => Boolean"))
    assert(Ref.Sort(ft).describe == Seq("sort", "(BigInt) => Boolean"))
    assert(Ref.Constructor(Some(id), ADTType(id, Seq())).describe == Seq("constructor", id.uniqueName, id.uniqueName))
    assert(Ref.Constructor(None, UnitType()).describe == Seq("constructor", "Unit"))
    assert(Ref.Selector(Some(id), ADTType(id, Seq()), 1).describe == Seq("selector", id.uniqueName, id.uniqueName, "1"))
    assert(Ref.Tester(None, UnitType()).describe == Seq("tester", "Unit"))
  }

  test("A CPC answer is unwrapped, and its errors and trusted steps are refused") {
    assert(Certificates.cpc("(\n(assume @p1 a)\n(step @p2 false :rule resolution)\n)") ==
      Right(Seq(parsed("(assume @p1 a)").head, parsed("(step @p2 false :rule resolution)").head)))
    assert(Certificates.cpc("(error \"no proof\")") == Left("cvc5 answered: (error \"no proof\")"))
    assert(Certificates.cpc("(\n(step @p1 a :rule trust)\n)") == Left("cvc5's proof has trusted steps"))
    assert(Certificates.cpc("((a)").isLeft)
    assert(Certificates.cpc("unsat") == Left("cvc5 answered: unsat"))
  }

  test("Configurations combine proofs, except with unsat assumptions") {
    assert(Configuration(proof = true) == Proof)
    assert(Configuration(model = true, proof = true) == ModelAndProof)
    assert(Configuration(unsatAssumptions = true, proof = true) == UnsatAssumptions)
    assert((Model `max` Proof) == ModelAndProof)
    assert((Simple `max` Proof) == Proof)
    assert((ModelAndProof `min` Model) == Model)
    assert((ModelAndProof `min` Proof) == Proof)
    assert((Model `min` Proof) == Simple)
  }

  test("Under a proof configuration, an unsat answer always has a proof or says why not") {
    val p = Right(ScriptProof(Seq(), Seq()))
    assert(Proof.cast(Unsat) == UnsatWithProof(Left("the solver does not produce proofs")))
    assert(ModelAndProof.cast(UnsatWithProof(p)) == UnsatWithProof(p))
    assert(Model.cast(UnsatWithProof(p)) == Unsat)
    assert(Proof.cast(Sat) == Sat)
  }
}
