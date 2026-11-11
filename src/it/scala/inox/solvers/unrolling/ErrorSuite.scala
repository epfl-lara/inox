/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** Errors are program points that are never reached: solvers drop the paths that reach one, and
  * evaluating one fails.
  */
class ErrorSuite extends UnrollingTestSuite {
  import trees._
  import dsl._
  import SolverResponses._

  override protected def optionMatrix = Seq(Seq(optCheckModels(true)))

  // An error on the negative inputs
  val positive = mkFunDef(FreshIdentifier("positive"))()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
      if_ (x <= E(BigInt(0))) {
        Error(IntegerType(), "negative input")
      } else_ {
        x
      }
    }))

  // An error that a recursive function reaches after a few calls
  val countdownID = FreshIdentifier("countdown")
  val countdown = mkFunDef(countdownID)()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
      if_ (x === E(BigInt(0))) {
        Error(IntegerType(), "reached zero")
      } else_ {
        E(countdownID)(x - E(BigInt(1))) + E(BigInt(1))
      }
    }))

  val symbols = NoSymbols.withFunctions(Seq(positive, countdown))
  val program = InoxProgram(symbols)

  test("paths through errors are infeasible") {
    val clause = positive(IntegerLiteral(-1)) === IntegerLiteral(0)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  test("paths around errors are kept") {
    val x = Variable.fresh("x", IntegerType())
    val SatWithModel(model) = SimpleSolverAPI(program.getSolver).solveSAT(positive(x) === IntegerLiteral(3)): @unchecked
    assert(model.vars.values.toSeq == Seq(IntegerLiteral(3)))
  }

  test("models avoid errors") {
    val x = Variable.fresh("x", IntegerType())
    val clause = positive(x) <= IntegerLiteral(1)
    val SatWithModel(model) = SimpleSolverAPI(program.getSolver).solveSAT(clause): @unchecked
    assert(model.vars.values.toSeq == Seq(IntegerLiteral(1)))
  }

  test("errors reached through recursion") {
    val clause = countdown(IntegerLiteral(2)) === IntegerLiteral(2)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  test("errors in lambdas are only reached when applied") { ctx ?=>
    // compares functions, which needs the intensional semantics of function equality
    given Context = ctx.withOpts(optFunctionEquality(FunctionEquality.Intensional))
    val f = Variable.fresh("f", FunctionType(Seq(IntegerType()), IntegerType()))
    val y = ValDef.fresh("y", IntegerType())
    val lambda = Lambda(Seq(y), IfExpr(y.toVariable > E(BigInt(0)), y.toVariable, Error(IntegerType(), "non-positive")))
    val clause = f === lambda && Application(f, Seq(IntegerLiteral(1))) === IntegerLiteral(1)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)

    val clause2 = f === lambda && Application(f, Seq(IntegerLiteral(0))) === IntegerLiteral(0)
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause2).isUNSAT)
  }

  test("evaluating an error fails") { ctx ?=>
    val evaluator = program.getEvaluator
    val res = evaluator.eval(positive(IntegerLiteral(-1)))
    assert(res.isInstanceOf[evaluators.EvaluationResults.RuntimeError], res)
    assert(evaluator.eval(positive(IntegerLiteral(2))).result == Some(IntegerLiteral(2)))
  }

  test("lambdas keep their errors") { ctx ?=>
    val evaluator = program.getEvaluator
    val lambda = Lambda(Seq(ValDef.fresh("y", IntegerType())), Error(IntegerType(), "never applied"))
    val res = evaluator.eval(lambda)
    assert(res.result.exists(_.isInstanceOf[Lambda]), res)
  }
}
