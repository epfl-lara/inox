/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package certificates

import org.scalatest.funsuite.AnyFunSuite

/** Certificates of refuted queries: the rules that the unrolling solver applied, and cvc5's proofs. */
class CertificateSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses._

  // sort Nat = Z | S(p: Nat)
  val natID = FreshIdentifier("Nat")
  val zID = FreshIdentifier("Z")
  val sID = FreshIdentifier("S")
  val pID = FreshIdentifier("p")
  val natSort = mkSort(natID)() { _ => Seq((zID, Seq()), (sID, Seq(ValDef(pID, T(natID)())))) }
  val Nat = T(natID)()
  def Z = ADT(zID, Seq(), Seq())
  def S(n: Expr) = ADT(sID, Seq(), Seq(n))

  // def size(n: Nat): BigInt = if (n is S) 1 + size(n.p) else 0
  val sizeID = FreshIdentifier("size")
  val sizeFd = mkFunDef(sizeID)() { _ => (Seq("n" :: Nat), IntegerType(), { case Seq(n) =>
    if_ (n.is(sID)) { E(BigInt(1)) + FunctionInvocation(sizeID, Seq(), Seq(n.getField(pID))) } else_ { E(BigInt(0)) }
  }) }

  // def pos(n: BigInt): BigInt = { assume(n > 0); n }
  val posID = FreshIdentifier("pos")
  val posFd = mkFunDef(posID)() { _ => (Seq("n" :: IntegerType()), IntegerType(), { case Seq(n) =>
    Assume(n > E(BigInt(0)), n)
  }) }

  // def app(f: BigInt => BigInt): BigInt = f(0)
  val appID = FreshIdentifier("app")
  val appFd = mkFunDef(appID)() { _ => (Seq("f" :: (IntegerType() =>: IntegerType())), IntegerType(), {
    case Seq(f) => f(E(BigInt(0)))
  }) }

  // def first[T](n: Nat, x: T, y: T): T = if (n is S) first(n.p, x, y) else x
  val firstID = FreshIdentifier("first")
  val firstFd = mkFunDef(firstID)("T") { case Seq(t) => (Seq("n" :: Nat, "x" :: t, "y" :: t), t, { case Seq(n, x, y) =>
    if_ (n.is(sID)) { FunctionInvocation(firstID, Seq(t), Seq(n.getField(pID), x, y)) } else_ { x }
  }) }

  val symbols: Symbols = NoSymbols.withSorts(Seq(natSort)).withFunctions(Seq(sizeFd, posFd, appFd, firstFd))
  val program = InoxProgram(symbols)
  given Symbols = symbols

  def ctx(options: OptionValue[?]*) = TestContext(Options(options))

  def cvc5(): Unit = assume(SolverFactory.hasCVC5, "needs cvc5")

  def check(expr: Expr, config: CheckConfiguration, solver: String = "smt-cvc5") = {
    val factory = SolverFactory(solver, program, ctx(optTimeout(scala.concurrent.duration.Duration(60, "s")), optProduceProofs(true)), force = true).withTimeout(60000)
    val s = factory.getNewSolver()
    try {
      s.assertCnstr(expr)
      (s.check(config): SolverResponse[program.Model, Set[Expr]])
    } finally factory.reclaim(s)
  }

  // size(S(S(Z))) unfolds size three times
  val sizeVC = Not(E(sizeID)(S(S(Z))) === E(BigInt(2)))

  test("A refutation with proofs holds the rules that the solver applied and cvc5's proof") {
    cvc5()
    for (vc <- Seq(sizeVC, Not(E(posID)(E(BigInt(1))) === E(BigInt(1))))) check(vc, Proof) match {
      case UnsatWithProof(Right(certificate: Certificate)) =>
        val text = certificate.toString
        assert(certificate.rules.exists(r => r.kind == "Unfold" && r.instance.nonEmpty), text)
        // the session's symbols stand for the program's functions and variables
        def refs(e: SExpr): Seq[Ref] = e match {
          case Sym(_, ref) => Seq(ref)
          case SList(es) => es.flatMap(refs)
          case _ => Seq()
        }
        val scriptRefs = certificate.proof.script.flatMap(refs)
        assert(scriptRefs.exists { case Ref.Function(id, _) => id == sizeID || id == posID; case _ => false }, scriptRefs)
        assert(scriptRefs.exists(_.isInstanceOf[Ref.Variable]), scriptRefs)
        assert(certificate.proof.cpc.flatMap(refs).nonEmpty, text)
        assert(certificate.proof.asserts.size == certificate.rules.flatMap(_.asserts).toSet.size + certificate.assumptions.size, text)
        assert(text.startsWith("(certificate\n(script\n(set-logic ALL)\n"), text)
        assert(text.contains("\n(templates\n(script\n"), text)
        assert(text.contains("\n(rules\n") && text.contains("\n(Root "), text)
        assert(text.contains("\n(Unfold (instance "), text)
        assert(text.contains("\n(cpc\n(declare-"), text)
        assert(text.contains("(assume "), text)
        assert(!text.contains(":rule trust"), text)
        assert(text.endsWith("))"), text)
      case UnsatWithProof(Left(why)) if why.startsWith("certificates need cvc5") => cancel(why)
      case other => fail(s"Unexpected answer: $other")
    }
  }

  test("A refutation with a polymorphic function has a certificate") {
    cvc5()
    val vc = Not(FunctionInvocation(firstID, Seq(IntegerType()), Seq(S(Z), E(BigInt(1)), E(BigInt(2)))) === E(BigInt(1)))
    check(vc, Proof) match {
      case UnsatWithProof(Right(_: Certificate)) =>
      case UnsatWithProof(Left(why)) if why.startsWith("certificates need cvc5") => cancel(why)
      case other => fail(s"Unexpected answer: $other")
    }
  }

  test("Without proofs, a refutation has none") {
    assume(SolverFactory.hasCVC5, "needs cvc5")
    assert(check(sizeVC, Model) == Unsat)
  }

  test("With proofs, a query with a model has one") {
    assume(SolverFactory.hasCVC5, "needs cvc5")
    val y = Variable.fresh("y", IntegerType())
    assert(check(y > E(BigInt(0)), ModelAndProof).isInstanceOf[SatWithModel[?]])
  }

  test("A solver that doesn't produce proofs says so") {
    check(sizeVC, Proof, "princess") match {
      case UnsatWithProof(Left(why)) => assert(why.contains("does not produce proofs"), why)
      case other => fail(s"Unexpected answer: $other")
    }
  }
}
