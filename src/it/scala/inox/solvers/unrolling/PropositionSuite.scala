/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

import ast.QuantifierMode

/** Checks that solvers answer the same whether quantifiers are booleans or propositions
  * (see [[inox.ast.Types.PropType]]), on queries that both modes accept. */
class PropositionSuite extends UnrollingTestSuite {
  import inox.trees._
  import dsl._

  override protected def optionMatrix = UnrollingTestSuite.combinations(
    Seq(optCheckModels(false), optCheckModels(true))
  )

  val fT = FunctionType(Seq(IntegerType()), IntegerType())

  // def pos(f: BigInt => BigInt): Prop = forall x. f(x) > 0
  val posID = FreshIdentifier("pos")
  def pos(tpe: Type) = mkFunDef(posID)() { _ =>
    (Seq("f" :: fT), tpe, { case Seq(f) => forall("x" :: IntegerType())(x => f(x) > E(BigInt(0))) })
  }

  val programs: Seq[(String, InoxProgram)] = Seq(
    "boolean" -> InoxProgram(NoSymbols.withFunctions(Seq(pos(BooleanType())))),
    "propositional" -> InoxProgram(
      NoSymbols.withFunctions(Seq(pos(PropType()))).withQuantifiers(QuantifierMode.Propositional))
  )

  val f = Variable.fresh("f", fT)
  val positive: Expr = forall("x" :: IntegerType())(x => f(x) > E(BigInt(0)))

  for ((mode, program) <- programs) {
    test(s"A quantifier is instantiated under $mode quantifiers") {
      val clause = positive && f(E(BigInt(3))) <= E(BigInt(0))
      assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
    }

    test(s"A negated quantifier has a counterexample under $mode quantifiers") {
      assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(positive)).isSAT)
    }

    test(s"A predicate definition is unfolded under $mode quantifiers") {
      val call = FunctionInvocation(posID, Seq(), Seq(f))
      assert(SimpleSolverAPI(program.getSolver).solveSAT(call && f(E(BigInt(3))) <= E(BigInt(0))).isUNSAT)
      assert(SimpleSolverAPI(program.getSolver).solveSAT(Not(call)).isSAT)
    }

    test(s"A refinement by a quantifier is assumed under $mode quantifiers") {
      val h = "h" :: fT
      val g = Variable.fresh("g", RefinementType(h, forall("x" :: IntegerType())(x => h.toVariable(x) > E(BigInt(0)))))
      assert(SimpleSolverAPI(program.getSolver).solveSAT(g(E(BigInt(3))) <= E(BigInt(0))).isUNSAT)
      assert(SimpleSolverAPI(program.getSolver).solveSAT(g(E(BigInt(3))) === E(BigInt(7))).isSAT)
    }

    test(s"An assumed quantifier is assumed under $mode quantifiers") {
      val clause = Assume(positive, f(E(BigInt(3))) <= E(BigInt(0)))
      assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
    }
  }

  test("A proposition is named by a let") {
    val program = programs.toMap.apply("propositional")
    val p = "p" :: PropType()
    val clause = Let(p, positive, p.toVariable && f(E(BigInt(3))) <= E(BigInt(0)))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(Let(p, positive, Not(p.toVariable))).isSAT)
  }

  test("A term that depends on a proposition is rejected") {
    val program = programs.toMap.apply("propositional")
    val clause = IfExpr(positive, f(E(BigInt(3))), E(BigInt(0))) === E(BigInt(1))
    intercept[program.symbols.TypeErrorException] {
      SimpleSolverAPI(program.getSolver).solveSAT(clause)
    }
  }
}
