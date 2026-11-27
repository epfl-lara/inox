/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package certificates

import org.scalatest.funsuite.AnyFunSuite

/** The proofs of cvc5's own answers, without the unrolling solver. */
class CVC5ProofSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._
  import SolverResponses._

  val program = InoxProgram(NoSymbols)
  val x = Variable.fresh("x", IntegerType())

  def check(config: CheckConfiguration, proofs: Boolean, exprs: Expr*): SolverResponse[Any, Any] = {
    assume(SolverFactory.hasCVC5, "needs cvc5")
    val ctx = TestContext(Options(Seq(optProduceProofs(proofs))))
    val p: program.type = program
    class Underlying(override val program: p.type)
      extends smtlib.SMTLIBSolver(program, ctx)(using program.getSemantics) with smtlib.CVC5Solver with smtlib.CVC5Certificates
    val s = new Underlying(p)
    try {
      exprs.foreach(s.assertCnstr)
      (s.check(config): SolverResponse[Any, Any])
    } finally s.free()
  }

  test("cvc5 answers an unsat check with its session and its proof") {
    check(Proof, true, x > E(BigInt(0)), x < E(BigInt(0))) match {
      case UnsatWithProof(Right(proof: ScriptProof)) =>
        assert(proof.asserts.size == 2, proof)
        // the session's symbol stands for the variable
        assert(proof.script.flatMap(_.symbols).exists(_.ref == Ref.Variable(x)), proof)
        assert(proof.cpc.exists { case SList(Atom("assume") +: _) => true; case _ => false }, proof)
        assert(!proof.toString.contains(":rule trust"), proof)
      case UnsatWithProof(Left(why)) if why.startsWith("certificates need cvc5") => cancel(why)
      case other => fail(s"Unexpected answer: $other")
    }
  }

  test("cvc5 without proof production says that it doesn't produce proofs") {
    assert(check(Proof, false, x > E(BigInt(0)), x < E(BigInt(0))) == UnsatWithProof(Left("the solver does not produce proofs")))
  }

  test("cvc5 with proof production answers without a proof under the other configurations") {
    assert(check(Simple, true, x > E(BigInt(0)), x < E(BigInt(0))) == Unsat)
    assert(check(ModelAndProof, true, x > E(BigInt(0))).isInstanceOf[SatWithModel[?]])
  }
}
