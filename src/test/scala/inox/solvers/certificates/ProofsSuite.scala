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

  // clauses c0, c1 asserted, then the assumptions a and r; a template t with parameter p and clause tc, of the expression tc
  import Certificates.{AppliedRule, Assumed}
  def refutation(rules: Seq[AppliedRule[String]]) = Certificates.Refutation(
    Seq("c0", "c1"), Seq(Assumed("a", false), Assumed("r", true)), Seq(Certificates.TemplateClauses(Seq("p"), Seq("tc"), Source.Expression("tc"))), rules)
  val x = inox.trees.Variable.fresh("x", inox.trees.IntegerType())
  val c0 = Sym("c0", Ref.Variable(x))
  val proof = ScriptProof(Seq(SList(Seq(Atom("assert"), c0)), asserting("c1"), asserting("a"), asserting("r")), parsed("(assume @p1 c0)"))
  def print(es: Seq[String]) = Certificates.Printed(es.map(Atom(_)),
    if (es.contains("p")) Seq(SList(Seq(Atom("declare-const"), Atom("p"), Atom("Bool")))) else Seq())

  // a printer that prints the terms with `terms` and the sources with `sources`, without declarations or sorts
  def printer(terms: Seq[String] => Certificates.Printed, sources: Seq[String] => Certificates.Printed) =
    new Certificates.Printer[String] {
      def printTerms(es: Seq[String]) = terms(es)
      def printSources(es: Seq[String]) = sources(es)
      def declarations = Seq()
      def sort(ref: Ref) = None
    }

  test("A certificate names the asserts of each rule, the templates and the assumptions") {
    val rules = Seq(
      AppliedRule("Root", Seq(Argument("start", Seq("c0"))), None, Seq("c0")),
      AppliedRule("Unfold", Seq(Argument("blocker", Seq("c0")), Argument("flag", Seq())), Some(Instance(0, Seq(Value("p", "c0")))), Seq("c1", "c1")))
    Certificates.certificate(proof, refutation(rules), printer(print, print)) match {
      case Right(c) =>
        assert(c.rules == Seq(
          Rule("Root", Seq(Argument("start", Seq(Atom("c0")))), None, Seq(0)),
          Rule("Unfold", Seq(Argument("blocker", Seq(Atom("c0"))), Argument("flag", Seq())),
            Some(Instance(0, Seq(Value(Atom("p"), Atom("c0"))))), Seq(1))))
        assert(c.templates == Seq(Template(Seq(Atom("p")), Seq(0), Source.Expression(Atom("tc")))))
        assert(c.assumptions == Assumptions(Seq(2), Seq(3)))
        assert(c.solverSymbols == Seq("c0" -> Ref.Variable(x)))
        assert(c.toString ==
          "(inox-certificate 5\n(script\n(assert c0)\n(assert c1)\n(assert a)\n(assert r)\n(check-sat)\n)\n" +
          "(templates\n(script\n(declare-const p Bool)\n(assert tc)\n)\n(0 (params p) (expression tc) 0)\n)\n" +
          "(rules\n(Root (args (start c0)) 0)\n(Unfold (args (blocker c0) (flag)) (instance 0 ((p c0))) 1)\n)\n" +
          "(assumptions (query 2) (complete 3))\n" +
          s"(solver-symbols\n(c0 variable \"${x.id.uniqueName}\" \"BigInt\")\n)\n" +
          "(source-definitions\n)\n(source-symbols\n)\n(simplifications\n(function-equality none)\n)\n" +
          "(cpc\n(assume @p1 c0)\n))")
      case Left(why) => fail(why)
    }
  }

  test("The source of a defined function prints its call and names, without its body") {
    val call = SList(Seq(Atom("f"), Atom("x")))
    assert(Source.Definition(call).toString == "(definition (f x))")
    assert(Source.Definition(call, Seq(Atom("l") -> Atom("b")), Seq(Atom("e") -> Atom("0"))).toString ==
      "(definition (f x) (names (l b)) (where (e 0)))")
    assert(Source.Function(call, Atom("b")).toString == "(function (f x) b)")
  }

  test("The symbols of the sources are apart from those of the session") {
    val y = inox.trees.Variable.fresh("y", inox.trees.IntegerType())
    val withSource = Certificates.Refutation(Seq("c0"), Seq(),
      Seq(Certificates.TemplateClauses(Seq("p"), Seq("tc"), Source.Expression("s"))),
      Seq(AppliedRule[String]("Root", Seq(), None, Seq("c0"))))
    val p = ScriptProof(Seq(SList(Seq(Atom("assert"), c0))), Seq())
    // the source's symbol has the text of a symbol of the session, for another variable
    def printSources(es: Seq[String]) = Certificates.Printed(es.map(_ => SList(Seq(Atom("assume"), Sym("c0", Ref.Variable(y)), Atom("true")))), Seq())
    Certificates.certificate(p, withSource, printer(print, printSources)) match {
      case Right(c) =>
        assert(c.templates.map(_.source.toString) == Seq("(expression (assume c0 true))"))
        assert(c.solverSymbols == Seq("c0" -> Ref.Variable(x)))
        assert(c.sourceSymbols == Seq("c0" -> Ref.Variable(y)))
        assert(c.toString.contains(s"\n(source-symbols\n(c0 variable \"${y.id.uniqueName}\" \"BigInt\")\n)\n"), c.toString)
      case Left(why) => fail(why)
    }
  }

  test("Symbols are described by their kind, identifiers and types") {
    import inox.trees._
    val id = FreshIdentifier("f")
    val ft = FunctionType(Seq(IntegerType()), BooleanType())
    assert(Ref.Function(id, Seq(IntegerType())).describe == Seq("function", id.uniqueName, "BigInt"))
    assert(Ref.Uninterpreted(id).describe == Seq("uninterpreted", id.uniqueName))
    assert(Ref.Uninterpreted(id, Seq(IntegerType())).describe == Seq("uninterpreted", id.uniqueName))
    assert(Ref.Lambda(ft).describe == Seq("application", "(BigInt) => Boolean"))
    assert(Ref.Sort(ft).describe == Seq("sort", "(BigInt) => Boolean"))
    assert(Ref.Constructor(Some(id), ADTType(id, Seq())).describe == Seq("constructor", id.uniqueName, id.uniqueName))
    assert(Ref.Constructor(None, UnitType()).describe == Seq("constructor", "Unit"))
    assert(Ref.Selector(Some(id), ADTType(id, Seq()), 1).describe == Seq("selector", id.uniqueName, id.uniqueName, "1"))
    assert(Ref.Tester(None, UnitType()).describe == Seq("tester", "Unit"))
  }

  test("A clause asserted twice is named by both asserts") {
    val twice = Certificates.Refutation(Seq("c0", "c0"), Seq(), Seq(), Seq(AppliedRule[String]("Root", Seq(), None, Seq("c0"))))
    val p = ScriptProof(Seq(asserting("c0"), asserting("c0")), Seq())
    assert(Certificates.certificate(p, twice, printer(print, print)).map(_.rules) == Right(Seq(Rule("Root", Seq(), None, Seq(0, 1)))))
  }

  test("A certificate needs one assert per clause and assumption") {
    val missing = ScriptProof(Seq(asserting("c0")), Seq())
    assert(Certificates.certificate(missing, refutation(Seq()), printer(print, print)) ==
      Left("the solver's session has 1 asserts, for 2 clauses and 2 assumptions"))
  }

  test("A certificate whose terms can't be printed says why") {
    val failing: Seq[String] => Certificates.Printed = _ => throw new IllegalStateException("no SMT-LIB form")
    val rules = Seq(AppliedRule[String]("Root", Seq(), None, Seq("c0", "c1")))
    assert(Certificates.certificate(proof, refutation(rules), printer(failing, failing)) ==
      Left("the certificate's terms or sources can't be printed in SMT-LIB (no SMT-LIB form)"))
  }

  test("A certificate needs each clause to be the clause of a rule") {
    val rules = Seq(AppliedRule[String]("Root", Seq(), None, Seq("c0")))
    assert(Certificates.certificate(proof, refutation(rules), printer(print, print)) ==
      Left("clause 1 of the solver's session is the clause of no rule"))
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
