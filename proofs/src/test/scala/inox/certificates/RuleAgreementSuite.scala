/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

import org.scalatest.funsuite.AnyFunSuite

/** The checker builds the clauses of each kind of rule as the solver's rule kernel does: for each
  * kind that doesn't instantiate a template, the clauses that `unrolling.RuleKernel` builds are
  * those that [[Checker]] builds from the arguments that the rule logs. */
class RuleAgreementSuite extends AnyFunSuite {
  import inox.trees._
  import Checker.{SExpr, Atom, SList}

  /** `e` as the s-expression that a certificate would print for it. */
  def sexpr(e: Expr): SExpr = e match {
    case v: Variable => Atom(v.id.uniqueName)
    case BooleanLiteral(b) => Atom(b.toString)
    case IntegerLiteral(i) => Atom(i.toString)
    case Not(e) => SList(List(Atom("not"), sexpr(e)))
    case And(es) => SList(Atom("and") :: es.map(sexpr).toList)
    case Or(es) => SList(Atom("or") :: es.map(sexpr).toList)
    case Implies(l, r) => SList(List(Atom("=>"), sexpr(l), sexpr(r)))
    case Equals(l, r) => SList(List(Atom("="), sexpr(l), sexpr(r)))
    case Application(f, args) => SList(Atom("apply") :: sexpr(f) :: args.map(sexpr).toList)
    case other => fail(s"Unexpected term: $other")
  }

  test("The checker builds the clauses of each kind of rule as the rule kernel does") {
    assume(solvers.SolverFactory.hasZ3, "needs z3")
    val program = InoxProgram(NoSymbols)
    val ctx = TestContext(Options(Seq(solvers.certificates.optProduceProofs(true))))
    val factory = solvers.SolverFactory("smt-z3", program, ctx, force = true)
    val solver = factory.getNewSolver()
    try {
      val t = solver.asInstanceOf[solvers.unrolling.UnrollingSolver].templates
      import t.Rule

      def enc(e: Expr): t.Encoded = e.asInstanceOf[t.Encoded]
      def tpe(tp: Type): t.program.trees.Type = tp.asInstanceOf[t.program.trees.Type]
      def bool(name: String): t.Encoded = enc(Variable.fresh(name, BooleanType()))
      def int(name: String): t.Encoded = enc(Variable.fresh(name, IntegerType()))
      def fun(name: String): t.Encoded = enc(Variable.fresh(name, FunctionType(Seq(), IntegerType())))

      val rules: Seq[Rule] = Seq(
        Rule.Define(None, bool("l"), enc(And(Variable.fresh("a", BooleanType()), Variable.fresh("b", BooleanType())))),
        Rule.Define(Some(bool("g")), bool("l"), bool("v")),
        Rule.Enables(bool("b"), bool("t")),
        Rule.Hypothesis(bool("l"), bool("c"), bool("f")),
        Rule.Root(bool("start")),
        Rule.Typed(bool("b"), bool("typing")),
        Rule.Holds(bool("b"), bool("q")),
        Rule.Unreachable(bool("l")),
        Rule.Unreachable(bool("l"), Some(bool("u"))),
        Rule.Decreases(bool("b"), bool("d"), None),
        Rule.Decreases(bool("b"), bool("d"), Some(bool("diverges"))),
        Rule.Congruence(Seq(bool("p1"), bool("p2"), bool("p3")), bool("r")),
        Rule.Witness(bool("start"), bool("differ"), None),
        Rule.Witness(bool("start"), bool("differ"), Some((bool("err1"), bool("err2")))),
        Rule.Reflexivity(tpe(IntegerType()), int("e1"), int("e2"), None),
        Rule.Reflexivity(tpe(IntegerType()), int("e1"), int("e2"), Some(bool("g"))),
        Rule.Symmetry(tpe(IntegerType()), bool("b"), int("e1"), int("e2")),
        Rule.Transitivity(tpe(IntegerType()), bool("g"), int("e1"), int("e2"), int("e3")),
        Rule.Dispatched(bool("b"), t.OpenOr("rest", t.AssumedComplete.ForModels)),
        Rule.DispatchFailure(bool("e"), bool("app"), bool("body")),
        Rule.SameLambda(bool("start"), fun("lambda"), fun("representative")),
        Rule.LambdaEquality(bool("b"), fun("l1"), fun("l2"), Some(bool("eqs")), true),
        Rule.LambdaEquality(bool("b"), fun("l1"), fun("l2"), None, true),
        Rule.LambdaEquality(bool("b"), fun("l1"), fun("l2"), Some(bool("eqs")), false),
        Rule.LambdaEquality(bool("b"), fun("l1"), fun("l2"), None, false))

      for (rule <- rules) {
        val args = rule.arguments.map { case (name, terms) =>
          SList(Atom(name) :: terms.map(e => sexpr(e.asInstanceOf[Expr])).toList)
        }.toList
        val built = rule.clauses.map(c => Checker.normal(sexpr(c.asInstanceOf[Expr]))).toSet
        val expected = Checker.ruleClauses(rule.productPrefix, args).map(Checker.normal).toSet
        assert(built == expected, s"for $rule")
      }
      // every kind that doesn't instantiate a template is covered
      assert(rules.map(_.productPrefix).toSet == Set("Define", "Enables", "Hypothesis", "Root", "Typed", "Holds", "Unreachable",
        "Decreases", "Congruence", "Witness", "Reflexivity", "Symmetry", "Transitivity", "Dispatched", "DispatchFailure",
        "SameLambda", "LambdaEquality"))
    } finally factory.reclaim(solver)
  }
}
