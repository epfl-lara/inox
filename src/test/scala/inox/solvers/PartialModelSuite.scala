/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

/** Only the semantics and solvers that can operate under a partial model accept models that
  * interpret functions. */
class PartialModelSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._

  val f = FreshIdentifier("f")

  // A function that makes an uninterpreted call to `f`
  val callF = mkFunDef(FreshIdentifier("callF"))()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
      UninterpretedCall(f, Seq(), Seq(x), FunctionType(Seq(IntegerType()), IntegerType())) }))

  val program = InoxProgram(NoSymbols.withFunctions(Seq(callF)))
  val outer: program.type = program
  given ctx: Context = TestContext.empty
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

  /** An evaluator whose solvers are those of [[plain]]. */
  val plainEvaluator = {
    class Impl(override val program: outer.type)(using override val semantics: outer.Semantics)
      extends evaluators.RecursiveEvaluator(program, ctx)
         with evaluators.HasDefaultGlobalContext
         with evaluators.HasDefaultRecContext
    new Impl(outer)(using plain.asInstanceOf[outer.Semantics])
  }

  val y = ValDef.fresh("y", IntegerType())
  val callsF = Forall(Seq(y), UninterpretedCall(f, Seq(), Seq(y.toVariable),
    FunctionType(Seq(IntegerType()), IntegerType())) === y.toVariable)
  val callsNothing = Forall(Seq(y), y.toVariable + E(BigInt(0)) === y.toVariable)

  test("evaluators solve for the foralls that call uninterpreted functions under the model") {
    val evaluator = program.getEvaluator
    assert(evaluator.eval(callsF, interpreting) == evaluators.EvaluationResults.Successful(E(true)))
  }

  test("semantics that can't solve under a model still solve for the foralls that call no uninterpreted function") {
    assert(plainEvaluator.eval(callsNothing, interpreting) == evaluators.EvaluationResults.Successful(E(true)))
  }

  val callsFThroughFunction = Forall(Seq(y), callF(y.toVariable) === y.toVariable)

  test("evaluators solve for the foralls that call uninterpreted functions through functions under the model") {
    val evaluator = program.getEvaluator
    assert(evaluator.eval(callsFThroughFunction, interpreting) == evaluators.EvaluationResults.Successful(E(true)))
  }

  for ((name, forall) <- Seq("directly" -> callsF, "through functions" -> callsFThroughFunction)) {
    test(s"semantics that can't solve under a model reject the foralls that call uninterpreted functions $name") {
      val res = scala.util.Try(plainEvaluator.eval(forall, interpreting))
      assert(res.failed.toOption.exists(_.getMessage.contains("interprets functions")) ||
        res.toOption.exists(r => !r.isInstanceOf[evaluators.EvaluationResults.Successful[?]] &&
          r.toString.contains("interprets functions")), res.toString)
    }
  }
}
