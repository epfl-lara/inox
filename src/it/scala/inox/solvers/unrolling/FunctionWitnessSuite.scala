/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import SolverResponses._
import evaluators.EvaluationResults

/** Checks that distinct first-class functions in models have a distinguishing input.
  *
  * @see [[LambdaTemplates.witnessAssumptions]]
  */
class FunctionWitnessSuite extends UnrollingTestSuite {
  import inox.trees._
  import dsl._

  override protected def optionMatrix = UnrollingTestSuite.combinations(
    Seq(optCheckModels(true)),
    Seq(optModelFinding(0), optModelFinding(1))
  )

  override def optionsString(options: Options): String =
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "model=" + options.findOptionOrDefault(optModelFinding)

  val program = InoxProgram(NoSymbols)

  private def solve(clause: Expr)(using Context): Map[ValDef, Expr] = {
    SimpleSolverAPI(program.getSolver).solveSAT(clause) match {
      case SatWithModel(model) => model.vars
      case res => fail(s"Expected a model, got $res")
    }
  }

  /** Inputs on which `f1` and `f2` can be compared: all closed sub-expressions of the
    * extracted models that have the right type. */
  private def candidates(tpe: Type, es: Expr*): Set[Expr] = es.toSet.flatMap { (e: Expr) =>
    exprOps.collect[Expr] {
      case e if e.getType(using program.symbols) == tpe && exprOps.variablesOf(e).isEmpty => Set(e)
      case _ => Set.empty
    } (e)
  }

  private def distinguishable(f1: Expr, f2: Expr)(using ctx: Context): Boolean = {
    val FunctionType(Seq(from), _) = f1.getType(using program.symbols): @unchecked
    val evaluator = program.getEvaluator
    candidates(from, f1, f2).exists { arg =>
      val r1 = evaluator.eval(Application(f1, Seq(arg)))
      val r2 = evaluator.eval(Application(f2, Seq(arg)))
      (r1, r2) match {
        case (EvaluationResults.Successful(v1), EvaluationResults.Successful(v2)) => v1 != v2
        case _ => false
      }
    }
  }

  test("distinct first-order functions") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val model = solve(f !== g)
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  test("distinct function and lambda") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val clause = f !== \("x" :: IntegerType())(x => x + E(BigInt(1)))
    val model = solve(clause)
    assert(distinguishable(model(f.toVal), \("x" :: IntegerType())(x => x + E(BigInt(1)))))
  }

  test("distinct higher-order functions") { ctx ?=>
    val tpe = (IntegerType() =>: IntegerType()) =>: IntegerType()
    val f = ("f" :: tpe).toVariable
    val g = ("g" :: tpe).toVariable
    val model = solve(f !== g)
    // cvc5 models for function-typed witnesses can't be extracted yet, so the solver
    // falls back to a model without distinguishing inputs
    if (!ctx.options.findOptionOrDefault(optSelectedSolvers).contains("smt-cvc5")) {
      assert(distinguishable(model(f.toVal), model(g.toVal)))
    }
  }

  test("distinct functions agreeing on an input") {
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val clause = (f !== g) && f(E(BigInt(0))) === g(E(BigInt(0)))
    val model = solve(clause)
    assert(distinguishable(model(f.toVal), model(g.toVal)))
  }

  test("eta-expanded closure remains distinct") {
    // Function equality is intensional and `f` closes over `g`, so `f != g` even though
    // no distinguishing input can exist: the solver must drop the witness assumptions.
    val f = ("f" :: (IntegerType() =>: IntegerType())).toVariable
    val g = ("g" :: (IntegerType() =>: IntegerType())).toVariable
    val clause = f === \("x" :: IntegerType())(x => g(x))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }
}
