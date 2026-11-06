/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

/** Checks the incremental solver interface (push/pop, assumptions and reset) on every solver,
  * including the `no-inc:` wrappers that replay the assertions in a fresh solver.
  */
class IncrementalSolverSuite extends SolverTestSuite {
  override protected def options = Seq(optCheckModels(true))

  import SolverTestSuite._
  import inox.trees.{given, _}
  import inox.trees.dsl.{given, _}
  import SolverResponses._

  override protected def solverInfos: Seq[SolverInfo] = {
    val nonIncremental = Set("unrollz3", "smt-z3", "smt-cvc4", "smt-cvc5")
    solvers ++ solvers.filter(info => nonIncremental(info.name)).map(info => info.copy(name = "no-inc:" + info.name))
  }

  val incID = FreshIdentifier("inc")
  val inc = mkFunDef(incID)() { _ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => x + IntegerLiteral(1) })
  }

  val boxID = FreshIdentifier("Box")
  val boxCons = FreshIdentifier("Box")
  val boxSort = mkSort(boxID)() { _ => Seq((boxCons, Seq(ValDef(FreshIdentifier("v"), IntegerType())))) }

  // unbox(b) = b.v + 0, so that the unrolling solver unfolds its calls
  val unboxID = FreshIdentifier("unbox")
  val unbox = mkFunDef(unboxID)() { _ => (
    Seq("b" :: T(boxID)()), IntegerType(), { case Seq(b) => b.getField(boxSort.constructors.head.fields.head.id) + E(BigInt(0)) })
  }

  override protected def symbols: Symbols = NoSymbols.withFunctions(Seq(inc, unbox)).withSorts(Seq(boxSort))
  given Symbols = symbols

  def withSolver(ctx: Context)(body: Solver { val program: InoxProgram } => Unit): Unit = {
    val factory = program.getSolver(ctx)
    val s = factory.getNewSolver()
    try body(s) finally factory.reclaim(s)
  }

  val x = Variable.fresh("x", Int32Type())

  def valueOf(s: Solver { val program: InoxProgram }, v: Variable): Option[Expr] = s.check(Model) match {
    case SatWithModel(model) => model.vars.get(v.toVal)
    case res => fail(s"Expected a model but got $res")
  }

  test("Push and pop") { ctx =>
    withSolver(ctx) { s =>
      s.assertCnstr(x > E(0))
      s.push()
      s.assertCnstr(x < E(0))
      assert(s.check(Simple).isUNSAT)
      s.pop()
      s.assertCnstr(x < E(2))
      assert(valueOf(s, x) == Some(Int32Literal(1)))
    }
  }

  test("Push and pop after an interrupt") { ctx =>
    withSolver(ctx) { s =>
      s.assertCnstr(x > E(0))
      // An interrupt can land while the unrolling solver pushes or pops, and the query
      // must then end as Unknown instead of throwing.
      s.interrupt()
      s.push()
      s.assertCnstr(x < E(0))
      s.pop()
      s.check(Simple)
    }
  }

  test("Function calls across push and pop", Feature.Integers) { ctx =>
    withSolver(ctx) { s =>
      val y = Variable.fresh("y", IntegerType())
      s.push()
      s.assertCnstr(Equals(inc(y), IntegerLiteral(5)))
      assert(valueOf(s, y) == Some(IntegerLiteral(4)))
      s.pop()
      s.assertCnstr(Equals(inc(inc(y)), IntegerLiteral(7)))
      assert(valueOf(s, y) == Some(IntegerLiteral(5)))
    }
  }

  // The unrolling templates are encoded once and reused, so the symbols they refer to (declared
  // while a scope was open) must remain valid after the scope is popped.
  test("Datatypes and lambdas across push and pop", Feature.Integers, Feature.ADTs, Feature.Functions) { ctx =>
    // `f == succ` compares functions, which needs a function equality other than the default
    withSolver(ctx.withOpts(unrolling.optFunctionEquality(unrolling.FunctionEquality.Intensional))) { s =>
      val y = Variable.fresh("y", IntegerType())
      val f = Variable.fresh("f", IntegerType() =>: IntegerType())
      val box = (v: Expr) => ADT(boxCons, Seq(), Seq(v))
      val succ = \("a" :: IntegerType())(a => a + E(BigInt(1)))
      s.push()
      s.assertCnstr(Equals(unbox(box(Application(succ, Seq(y)))), E(BigInt(5))))
      assert(valueOf(s, y) == Some(IntegerLiteral(4)))
      s.pop()
      s.assertCnstr(Equals(f, succ))
      s.assertCnstr(Equals(unbox(box(Application(f, Seq(y)))), E(BigInt(7))))
      assert(valueOf(s, y) == Some(IntegerLiteral(6)))
    }
  }

  test("Check with assumptions") { ctx =>
    withSolver(ctx) { s =>
      val b1 = Variable.fresh("b1", BooleanType())
      val b2 = Variable.fresh("b2", BooleanType())
      val b3 = Variable.fresh("b3", BooleanType())
      s.assertCnstr(b1 ==> (x > E(0)))
      s.assertCnstr(b2 ==> (x < E(0)))
      s.assertCnstr(b3 ==> Equals(x, E(0)))

      s.checkAssumptions(All)(Set(b1, b2)) match {
        // solvers may return an empty core, but never anything else than the assumptions
        case UnsatWithAssumptions(core) => assert(core.subsetOf(Set(b1, b2)), s"Unexpected core $core")
        case res => fail(s"Expected unsat with assumptions but got $res")
      }
      s.checkAssumptions(Model)(Set(b1, Not(b2))) match {
        case SatWithModel(model) => assert(model.vars.get(x.toVal).exists { case Int32Literal(v) => v > 0 case _ => false })
        case res => fail(s"Expected a model but got $res")
      }
      assert(s.checkAssumptions(Simple)(Set(b3)).isSAT)
    }
  }

  test("Reset") { ctx =>
    withSolver(ctx) { s =>
      s.assertCnstr(x > E(0))
      s.assertCnstr(x < E(0))
      assert(s.check(Simple).isUNSAT)
      try {
        s.reset()
      } catch {
        // solvers may refuse to reset, but must otherwise forget the previous constraints
        case _: CantResetException => cancel(s"${s.name} can't be reset")
      }
      s.assertCnstr(Equals(x, E(3)))
      assert(valueOf(s, x) == Some(Int32Literal(3)))
    }
  }

  test("Branches and function calls after a reset", Feature.Integers) { ctx =>
    withSolver(ctx) { s =>
      val y = Variable.fresh("y", IntegerType())
      s.assertCnstr(Equals(inc(y), IntegerLiteral(5)))
      assert(valueOf(s, y) == Some(IntegerLiteral(4)))
      try {
        s.reset()
      } catch {
        case _: CantResetException => cancel(s"${s.name} can't be reset")
      }
      s.assertCnstr(if_ (x > E(0)) { Equals(inc(y), IntegerLiteral(7)) } else_ { Equals(inc(inc(y)), IntegerLiteral(7)) })
      s.assertCnstr(x < E(0))
      assert(valueOf(s, y) == Some(IntegerLiteral(5)))
    }
  }
}
