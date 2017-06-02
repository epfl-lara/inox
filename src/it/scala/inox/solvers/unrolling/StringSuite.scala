/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

class StringSuite extends SolvingTestSuite {
  import trees._
  import dsl._

  import SolverResponses._

  override def configurations = for {
    solverName  <- Seq("nativez3", "unrollz3", "smt-z3", "smt-cvc4", "princess")
  } yield Seq(
    optSelectedSolvers(Set(solverName)),
    optCheckModels(true)
  )

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  test("Empty string model") { ctx =>
    val program = InoxProgram(ctx, NoSymbols)
    val v = Variable.fresh("v", StringType)
    val clause = Equals(v, StringLiteral(""))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Non-empty string model") { ctx =>
    val program = InoxProgram(ctx, NoSymbols)
    val v = Variable.fresh("v", StringType)
    val clause = Not(Equals(v, StringLiteral("")))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Ground equality") { ctx =>
    val program = InoxProgram(ctx, NoSymbols)
    val clause = Equals(StringLiteral(""), StringLiteral(""))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Ground dis-equality") { ctx =>
    val program = InoxProgram(ctx, NoSymbols)
    val clause = Not(Equals(StringLiteral(""), StringLiteral("")))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isUNSAT)
  }

  test("Positive length") { ctx =>
    val program = InoxProgram(ctx, NoSymbols)
    val v = Variable.fresh("v", StringType)
    val clause = GreaterThan(StringLength(v), IntegerLiteral(BigInt(0)))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Non-ASCII string encoding") { ctx =>
    val program = InoxProgram(ctx, NoSymbols)
    val v = Variable.fresh("v", StringType)
    val clause = Equals(v, StringLiteral("abéà"))
    assert(SimpleSolverAPI(program.getSolver).solveSAT(clause).isSAT)
  }

  test("Non-ASCII string length") { ctx =>
    val program = InoxProgram(ctx, NoSymbols)
    val v = Variable.fresh("v", IntegerType)
    val clause = Equals(v, StringLength(StringLiteral("abéà")))
    SimpleSolverAPI(program.getSolver).solveSAT(clause) match {
      case SatWithModel(model) =>
        assert(model.vars.get(v.toVal) == Some(IntegerLiteral(BigInt(4))))
      case _ =>
        fail("Expected sat-with-model")
    }
  }

  test("String with newline") { ctx =>
    val program = InoxProgram(ctx, NoSymbols)
    val v = Variable.fresh("r", StringType)
    val clause = Equals(v, StringLiteral("\n"))
    SimpleSolverAPI(program.getSolver).solveSAT(clause) match {
      case SatWithModel(model) =>
        assert(model.vars.get(v.toVal) == Some(StringLiteral("\n")))
      case _ =>
        fail("Expected sat-with-model")
    }
  }
}
