/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class MinimizerSuite extends SolvingTestSuite with DatastructureUtils {
  import trees._
  import dsl._
  import SolverResponses._

  override def configurations = Seq(Seq(optSelectedSolvers(Set("smt-z3-min"))))

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  implicit val symbols: inox.trees.Symbols = NoSymbols

  val program = inox.Program(inox.trees)(symbols)

  test("automated minimization of n times n") { implicit ctx =>
    val x = Variable.fresh("x", Int32Type())
    val prop = GreaterEquals(Times(x, x), Int32Literal(10))

    val factory = SolverFactory.optimizer(program, ctx)
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(Not(prop))
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
}
