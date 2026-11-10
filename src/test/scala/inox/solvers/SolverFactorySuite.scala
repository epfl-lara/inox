/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

/** Selection of solvers by name and from the options. */
class SolverFactorySuite extends AnyFunSuite {
  import inox.trees._
  import SolverResponses._

  val program = InoxProgram(NoSymbols)
  val x = Variable.fresh("x", IntegerType())
  val constraint = And(GreaterThan(x, IntegerLiteral(1)), LessThan(x, IntegerLiteral(3)))

  def ctx(solvers: String*) = TestContext(Options(Seq(optSelectedSolvers(solvers.toSet))))

  private def solves(factory: SolverFactory { val program: SolverFactorySuite.this.program.type }): Unit = {
    val api = factory.toAPI
    api.solveSAT(constraint) match {
      case SatWithModel(model) => assert(model.vars(x.toVal) == IntegerLiteral(2))
      case res => fail(s"Unexpected result $res with ${factory.name}")
    }
    factory.shutdown()
  }

  test("A portfolio of the selected solvers") {
    val factory = SolverFactory(program, ctx("smt-z3", "princess"))
    assert(factory.name.startsWith("Pfolio("))
    solves(factory)

    val fromSettings = SolverFactory.getFromSettings(program, ctx("smt-z3", "princess"))(transformers.ProgramEncoder.empty(program))(using program.getSemantics)
    assert(fromSettings.name.startsWith("Pfolio("))
  }

  test("The default solvers") {
    solves(SolverFactory(program, TestContext.empty))
    val fromSettings = SolverFactory.getFromSettings(program, TestContext.empty)(transformers.ProgramEncoder.empty(program))(using program.getSemantics)
    solves(fromSettings)
  }

  test("A z3 executable given by its path") {
    solves(SolverFactory("smt-z3:z3", program, TestContext.empty))
    solves(SolverFactory("no-inc:smt-z3:z3", program, TestContext.empty))
    val ex = intercept[FatalError](SolverFactory("smt-z3:/no/such/z3", program, TestContext.empty))
    assert(ex.getMessage.contains("Unknown solver: /no/such/z3"))
  }

  test("Non-incremental solvers") {
    // The native z3 library isn't available on every platform.
    val native = if (SolverFactory.hasNativeZ3) Seq("no-inc:unrollz3") else Seq()
    for (name <- Seq("no-inc:smt-z3", "no-inc:smt-cvc5") ++ native) {
      val factory = SolverFactory(name, program, TestContext.empty, force = true)
      solves(factory)
    }
    val ex = intercept[FatalError](SolverFactory("no-inc:princess", program, TestContext.empty))
    assert(ex.getMessage.contains("Non incremental mode is not available"))
  }

  test("Unknown and missing solvers") {
    assert(intercept[FatalError](SolverFactory("no-such-solver", program, TestContext.empty)).getMessage.contains("Unknown solver"))
    assert(intercept[FatalError](SolverFactory(program, ctx())).getMessage.contains("No selected solver"))
    assert(intercept[FatalError](
      SolverFactory.getFromSettings(program, ctx())(transformers.ProgramEncoder.empty(program))(using program.getSemantics)
    ).getMessage.contains("No selected solver"))
    assert(intercept[FatalError](SolverFactory.optimizer(program, ctx())).getMessage.contains("No selected solver"))
    assert(intercept[FatalError](SolverFactory.optimizer(program, ctx("smt-z3", "nativez3"))).getMessage.contains("portfolio"))
  }

  test("Optimizers") {
    val opt = SolverFactory.optimizer(program, ctx("smt-z3"))
    assert(opt.name.contains("z3"))
    if (SolverFactory.hasNativeZ3) {
      val opt2 = SolverFactory.optimizer(program, ctx("nativez3-opt"))
      assert(opt2.name.contains("z3"))
    }
  }
}
