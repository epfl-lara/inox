/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class OptimizerSuite extends TestSuite with DatastructureUtils {
  import trees._
  import dsl._
  import SolverResponses._

  override def configurations =
    for (nme <- Seq("nativez3-opt", "smt-z3-opt")) yield {
      Seq(optSelectedSolvers(Set(nme)))
    }

  override def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head
  }

  implicit val symbols: inox.trees.Symbols = NoSymbols

  val program = inox.Program(inox.trees)(symbols)

  test("unsatisfiable soft constraint") { ctx ?=>
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
          case IntegerLiteral(n) => assert(n > 10)
        }
        case _ =>
          fail("Expected sat-with-model")
      }
    } finally {
      factory.reclaim(optimizer)
    }
  }

  test("n times n, minimize") { ctx ?=>
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

  test("n times n, maximize") { ctx ?=>
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

  def withOptimizer(body: AbstractOptimizer & Solver { val program: OptimizerSuite.this.program.type; type Trees = Expr } => Unit)(using ctx: Context): Unit = {
    val factory = SolverFactory.optimizer(program, ctx)
    val optimizer = factory.getNewSolver()
    try body(optimizer) finally factory.reclaim(optimizer)
  }

  def valueOf(optimizer: Solver { val program: OptimizerSuite.this.program.type }, v: Variable): Expr =
    optimizer.check(Model) match {
      case SatWithModel(model) => model.vars(v.toVal)
      case res => fail(s"Expected sat-with-model but got $res")
    }

  test("the heaviest soft constraint wins") { ctx ?=>
    val x = Variable.fresh("x", IntegerType())
    withOptimizer { optimizer =>
      optimizer.assertCnstr(Equals(x, IntegerLiteral(1)), 1)
      optimizer.assertCnstr(Equals(x, IntegerLiteral(2)), 5)
      optimizer.assertCnstr(Equals(x, IntegerLiteral(3)), 2, "other")
      assert(valueOf(optimizer, x) == IntegerLiteral(2))
    }
  }

  test("soft constraints in a group") { ctx ?=>
    val x = Variable.fresh("x", IntegerType())
    withOptimizer { optimizer =>
      optimizer.assertCnstr(GreaterThan(x, IntegerLiteral(0)))
      optimizer.assertCnstr(Equals(x, IntegerLiteral(-1)), 10, "g")
      optimizer.assertCnstr(Equals(x, IntegerLiteral(4)), 1, "g")
      assert(valueOf(optimizer, x) == IntegerLiteral(4))
    }
  }

  test("objectives over function calls") { ctx ?=>
    // Keep the objective linear: Z3 does not optimize non-linear terms.
    val succID = FreshIdentifier("succ")
    val succ = mkFunDef(succID)() { _ => (Seq("y" :: IntegerType()), IntegerType(), { case Seq(y) => Plus(y, IntegerLiteral(1)) }) }
    val fProgram = inox.Program(inox.trees)(NoSymbols.withFunctions(Seq(succ)))
    val x = Variable.fresh("x", IntegerType())
    val factory = SolverFactory.optimizer(fProgram, ctx)
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(GreaterEquals(x, IntegerLiteral(3)))
      optimizer.minimize(FunctionInvocation(succID, Seq(), Seq(x)))
      optimizer.check(Model) match {
        case SatWithModel(model) => assert(model.vars(x.toVal) == IntegerLiteral(3))
        case res => fail(s"Expected sat-with-model but got $res")
      }
      optimizer.assertCnstr(LessThan(FunctionInvocation(succID, Seq(), Seq(x)), x))
      assert(optimizer.check(Model).isUNSAT)
    } finally {
      factory.reclaim(optimizer)
    }
  }

  test("unsatisfiable function calls, unrolling unsat assumptions") { ctx ?=>
    val succID = FreshIdentifier("succ")
    val succ = mkFunDef(succID)() { _ => (Seq("y" :: IntegerType()), IntegerType(), { case Seq(y) => Plus(y, IntegerLiteral(1)) }) }
    val fProgram = inox.Program(inox.trees)(NoSymbols.withFunctions(Seq(succ)))
    val x = Variable.fresh("x", IntegerType())
    val factory = SolverFactory.optimizer(fProgram, ctx.withOpts(optUnrollAssumptions(true)))
    val optimizer = factory.getNewSolver()
    try {
      optimizer.assertCnstr(LessThan(FunctionInvocation(succID, Seq(), Seq(x)), x))
      optimizer.minimize(x)
      assert(optimizer.check(Model).isUNSAT)
    } finally {
      factory.reclaim(optimizer)
    }
  }

  test("push, pop and assumptions") { ctx ?=>
    val x = Variable.fresh("x", IntegerType())
    val b = Variable.fresh("b", BooleanType())
    withOptimizer { optimizer =>
      optimizer.assertCnstr(LessEquals(x, IntegerLiteral(5)))
      optimizer.push()
      optimizer.assertCnstr(GreaterThan(x, IntegerLiteral(5)))
      assert(optimizer.check(Simple).isUNSAT)
      optimizer.pop()
      assert(optimizer.check(Simple).isSAT)

      optimizer.assertCnstr(Implies(b, GreaterThan(x, IntegerLiteral(10))))
      assert(optimizer.checkAssumptions(Simple)(Set(b)).isUNSAT)
      optimizer.checkAssumptions(Model)(Set(Not(b))) match {
        case SatWithModel(model) => model.vars(x.toVal) match {
          case IntegerLiteral(n) => assert(n <= 5)
          case v => fail(s"Unexpected value $v")
        }
        case res => fail(s"Expected sat-with-model but got $res")
      }
    }
  }

  test("checks without models") { ctx ?=>
    val x = Variable.fresh("x", IntegerType())
    withOptimizer { optimizer =>
      optimizer.assertCnstr(GreaterThan(x, IntegerLiteral(0)))
      optimizer.minimize(x)
      assert(optimizer.check(Simple).isSAT)
      optimizer.assertCnstr(LessThan(x, IntegerLiteral(0)))
      assert(optimizer.check(Simple).isUNSAT)
    }(using ctx.withOpts(optIgnoreModels(true)))
  }

  test("interrupted checks are unknown") { ctx ?=>
    val x = Variable.fresh("x", IntegerType())
    withOptimizer { optimizer =>
      optimizer.assertCnstr(GreaterThan(x, IntegerLiteral(0)))
      optimizer.interrupt()
      assert(!optimizer.check(Model).isSAT)
    }
  }
}
