/* Copyright 2009-2024 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.Tag

class InvariantSolverSuite extends AnyFunSuite {
  import inox.trees._
  import dsl._

  val ctx = TestContext.empty
  val p = InoxProgram(NoSymbols)

  val solverOpts = List(
    (() => SolverFactory.hasZ3, "inv-z3"),
    (() => true, "inv-eld"),
  )

  val solverNames = solverOpts.flatMap {case (cond, name) => if cond() then List(name) else Nil}

  def getSolver(ctx: Context) =
    SimpleSolverAPI(p.getSolver(ctx))

  protected def test(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    for
      sname <- solverNames
      ctx = TestContext(Options(Seq(optSelectedSolvers(Set(sname)))))
    do
      super.test(s"$name ($sname)", tags*) {
        body(ctx)
      }
  }

  test("Validity of true") { ctx =>
    val solver = getSolver(ctx)
    solver.solveVALID(BooleanLiteral(true)) match {
      case Some(true) => ()
      case Some(false) => fail("True is not valid")
      case None => fail("Solver returned unknown")
    }
  }

  test("Unsatisfiability of false") { ctx =>
    val solver = getSolver(ctx)
    solver.solveSAT(BooleanLiteral(false)) match {
      case SolverResponses.Unsat => ()
      case SolverResponses.SatWithModel(_) => fail("False is not invalid")
      case _ => fail("Solver returned unknown response")
    }
  }

  test("Integer arithmetic") { ctx =>
    val solver = getSolver(ctx)
    val x = Variable.fresh("x", IntegerType())
    val y = Variable.fresh("y", IntegerType())
    val z = Variable.fresh("z", IntegerType())

    val eqs = List(
      x === y + z,
      y === IntegerLiteral(1),
      z === IntegerLiteral(2)
    )

    solver.solveSAT(andJoin(eqs)) match {
      case SolverResponses.SatWithModel(model) => ()
      case SolverResponses.Unsat => fail("Trivial integer arithmetic is unsat")
      case _ => fail("Solver returned unknown response")
    }
  }
}
