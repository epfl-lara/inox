/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class OptimizerSuite extends SolvingTestSuite with DatastructureUtils {
  import trees._
  import dsl._
  import SolverResponses._

  override def configurations =
    for (nme <- Seq(/*"nativez3-opt", */"smt-z3-opt")) yield {
      Seq(optSelectedSolvers(Set(nme)))
    }

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  implicit val symbols: inox.trees.Symbols = NoSymbols

  val program = inox.Program(inox.trees)(symbols)

  test("unsatisfiable soft constraint") { implicit ctx =>
    val v = Variable.fresh("x", IntegerType())
    val clause = GreaterThan(v, IntegerLiteral(BigInt(10)))
    val softClause = GreaterThan(IntegerLiteral(BigInt(10)), v)

    val factory = SolverFactory.optimizer(program, ctx)
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(clause)
      optimizer.assertCnstr(softClause, 1)
      optimizer.check(Model) match {
        case SatWithModel(model) =>  model.vars.get(v.toVal).get match {
          case IntegerLiteral(n) => n > 10
        }
        case _ =>
          fail("Expected sat-with-model")
      }
    } finally {
      factory.reclaim(optimizer)
    }
  }

  test("n times n, minimize") { implicit ctx =>
    val x = Variable.fresh("x", Int32Type())
    val prop = GreaterEquals(Times(x, x), Int32Literal(10))

    val factory = SolverFactory.optimizer(program, ctx)
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(Not(prop))
      optimizer.minimize(x)
      optimizer.check(Model) match {
        case SatWithModel(model) =>
          model.vars.get(x.toVal).get match {
            case Int32Literal(c) => assert(c == 0)
          }
        case _ =>
          fail("Expected sat-with-model")
      }
    } finally {
      factory.reclaim(optimizer)
    }
  }

  test("n times n, maximize") { implicit ctx =>
    val x = Variable.fresh("x", IntegerType())
    val prop = GreaterEquals(Times(x, x), IntegerLiteral(10))

    val factory = SolverFactory.optimizer(program, ctx)
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(Not(prop))
      optimizer.maximize(x)
      optimizer.check(Model) match {
        case SatWithModel(model) =>
          model.vars.get(x.toVal).get match {
            case IntegerLiteral(c) => assert(c == 3)
          }
        case _ =>
          fail("Expected sat-with-model")
      }
    } finally {
      factory.reclaim(optimizer)
    }
  }
}
