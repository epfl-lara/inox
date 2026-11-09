/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

/** Only the semantics and solvers that can operate under a partial model accept models that
  * interpret functions. */
class PartialModelSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._

  val program = InoxProgram(NoSymbols)
  val outer: program.type = program
  given ctx: Context = TestContext.empty

  val f = FreshIdentifier("f")
  val x = ValDef.fresh("x", IntegerType())
  val interpreting = inox.Model(program)(Map.empty, Map((f, Seq()) -> Lambda(Seq(x), x.toVariable)))
  val empty = inox.Model.empty(program)

  /** Semantics that don't override the creation of solvers under a model. */
  val plain = new inox.Semantics { self =>
    val trees: inox.trees.type = inox.trees
    val symbols: outer.symbols.type = outer.symbols
    val program: Program { val trees: inox.trees.type; val symbols: outer.symbols.type } = outer

    protected def createSolver(ctx: Context): SolverFactory {
      val program: self.program.type
      type S <: combinators.TimeoutSolver { val program: self.program.type }
    } = SolverFactory(self.program, ctx)

    protected def createEvaluator(ctx: Context): evaluators.DeterministicEvaluator {
      val program: self.program.type
    } = evaluators.RecursiveEvaluator(self.program, ctx)
  }

  test("semantics that can't solve under a model reject models that interpret functions") {
    val e = intercept[FatalError](plain.getSolver(interpreting.asInstanceOf[plain.program.Model]))
    assert(e.getMessage.contains("interprets functions"), e.getMessage)
  }

  test("semantics that can't solve under a model accept models without interpretations") {
    assert(plain.getSolver(empty.asInstanceOf[plain.program.Model]).name == plain.getSolver.name)
  }

  test("inox semantics solve under models that interpret functions") {
    program.getSemantics.getSolver(interpreting)
    program.getSemantics.getSolver(empty)
  }

  for (name <- Seq("eval", "inv-z3")) {
    test(s"solver $name rejects models that interpret functions") {
      val e = intercept[FatalError](SolverFactory.getFromName(name, force = true)(program, ctx, Some(interpreting))(
        transformers.ProgramEncoder.empty(program))(using program.getSemantics))
      assert(e.getMessage.contains(name), e.getMessage)
    }

    test(s"solver $name accepts models without interpretations") {
      SolverFactory.getFromName(name, force = true)(program, ctx, Some(empty))(
        transformers.ProgramEncoder.empty(program))(using program.getSemantics)
      SolverFactory.getFromName(name, force = true)(program, ctx)(
        transformers.ProgramEncoder.empty(program))(using program.getSemantics)
    }
  }

  test("unrolling solvers accept models that interpret functions") {
    SolverFactory.getFromName("smt-z3", force = true)(program, ctx, Some(interpreting))(
      transformers.ProgramEncoder.empty(program))(using program.getSemantics)
  }
}
