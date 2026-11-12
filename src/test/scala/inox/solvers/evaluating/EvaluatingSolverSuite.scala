/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package evaluating

import org.scalatest.funsuite.AnyFunSuite

/** The `eval` solver decides ground constraints with the evaluator and answers
  * Unknown for everything else.
  */
class EvaluatingSolverSuite extends AnyFunSuite {
  import inox.trees.{given, _}
  import inox.trees.dsl._
  import SolverResponses._

  val doubleID = FreshIdentifier("double")
  val double = mkFunDef(doubleID)() { _ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) => x + x })
  }

  val symbols = NoSymbols.withFunctions(Seq(double))
  val program = InoxProgram(symbols)
  given Symbols = symbols

  val ctx = TestContext(Options(Seq(optSelectedSolvers(Set("eval")))))
  val factory = SolverFactory("eval", program, ctx, force = true)

  def withSolver(body: Solver { val program: InoxProgram } => Unit): Unit = {
    val s = factory.getNewSolver()
    try body(s) finally factory.reclaim(s)
  }

  val one = IntegerLiteral(1)
  val two = IntegerLiteral(2)
  val x = Variable.fresh("x", IntegerType())

  test("The factory is named after the solver") {
    assert(factory.name == "eval")
    withSolver(s => assert(s.name == "eval"))
  }

  test("True ground constraints are satisfiable") {
    withSolver { s =>
      s.assertCnstr(Equals(double(one), two))
      s.assertCnstr(LessThan(one, two))
      assert(s.check(Simple) == Sat)
    }
  }

  test("A false ground constraint is unsatisfiable") {
    withSolver { s =>
      s.assertCnstr(LessThan(one, two))
      s.assertCnstr(Equals(double(one), one))
      assert(s.check(Simple) == Unsat)
    }
  }

  test("Satisfiable checks return an empty model") {
    withSolver { s =>
      s.assertCnstr(BooleanLiteral(true))
      s.check(Model) match {
        case SatWithModel(model) => assert(model.vars.isEmpty && model.interpretations.isEmpty)
        case res => fail(s"Expected a model, got $res")
      }
    }
  }

  test("Constraints with free variables are unknown") {
    withSolver { s =>
      s.assertCnstr(Equals(x, x))
      assert(s.check(Simple) == Unknown)
      assert(s.check(Model) == Unknown)
    }
  }

  test("Push and pop scope the constraints") {
    withSolver { s =>
      s.assertCnstr(BooleanLiteral(true))
      s.push()
      s.assertCnstr(BooleanLiteral(false))
      assert(s.check(Simple) == Unsat)
      s.pop()
      assert(s.check(Simple) == Sat)
    }
  }

  test("Reset drops every constraint") {
    withSolver { s =>
      s.assertCnstr(BooleanLiteral(false))
      s.reset()
      assert(s.check(Simple) == Sat)
    }
  }

  test("Assumptions are checked without being asserted") {
    withSolver { s =>
      s.assertCnstr(Equals(double(one), two))
      assert(s.checkAssumptions(Simple)(Set(BooleanLiteral(false))) == Unsat)
      assert(s.checkAssumptions(Simple)(Set(BooleanLiteral(true))) == Sat)
      assert(s.check(Simple) == Sat)
      assert(s.checkAssumptions(Simple)(Set(Equals(x, one))) == Unknown)
    }
  }

  test("Unsatisfiable assumptions can be requested with their core") {
    withSolver { s =>
      val assumption = Equals(double(one), one)
      s.checkAssumptions(UnsatAssumptions)(Set(assumption)) match {
        case UnsatWithAssumptions(core) => assert(core == Set(assumption))
        case res => fail(s"Expected unsat assumptions, got $res")
      }
      assert(s.checkAssumptions(All)(Set(BooleanLiteral(true), assumption)) == UnsatWithAssumptions(Set(assumption)))
      assert(s.checkAssumptions(UnsatAssumptions)(Set(BooleanLiteral(true))) == Sat)
      assert(s.checkAssumptions(All)(Set(BooleanLiteral(true))).isInstanceOf[SatWithModel[?]])
    }
  }

  test("Unsatisfiable constraints need no assumption in the core") {
    withSolver { s =>
      s.assertCnstr(BooleanLiteral(false))
      assert(s.checkAssumptions(UnsatAssumptions)(Set(BooleanLiteral(true))) == UnsatWithAssumptions(Set()))
    }
  }

  test("The solver works through the simple API") {
    val api = SimpleSolverAPI(factory)
    assert(api.solveVALID(Equals(double(two), IntegerLiteral(4))) == Some(true))
    assert(api.solveVALID(Equals(double(two), two)) == Some(false))
    assert(api.solveVALID(Equals(x, x)) == None)
  }

  test("Runtime errors during evaluation are unknown") {
    withSolver { s =>
      s.assertCnstr(Equals(Division(one, IntegerLiteral(0)), one))
      assert(s.check(Simple) == Unknown)
    }
  }

  test("Runtime errors are reported unless errors are silent") {
    val reporter = new TestSilentReporter
    val loud = Context(reporter, new utils.InterruptManager(reporter), Options(Seq(optSilentErrors(false))))
    val f = SolverFactory("eval", program, loud, force = true)
    val s = f.getNewSolver()
    try {
      s.assertCnstr(Equals(Division(one, IntegerLiteral(0)), one))
      assert(s.check(Simple) == Unknown)
      assert(reporter.lastErrors.exists(_.contains("Runtime error during evaluation")))
    } finally f.reclaim(s)
  }

  /** A reporter that records errors and debug messages. */
  class RecordingReporter(sections: Set[DebugSection]) extends DefaultReporter(sections) {
    val messages = scala.collection.mutable.ListBuffer.empty[Message]
    override def doEmit(msg: Message): Unit = messages += msg
    override def doEmit(msg: ProgressMessage, prevLength: Int): String = ""
    override def clearProgress(): Unit = ()
    def errors = messages.filter(_.severity == ERROR).map(_.msg.toString)
  }

  def loudSolver(reporter: Reporter) = {
    val loud = Context(reporter, new utils.InterruptManager(reporter), Options(Seq(optSilentErrors(false), optSelectedSolvers(Set("eval")))))
    SolverFactory("eval", program, loud, force = true).getNewSolver()
  }

  test("Declaring variables is accepted") {
    withSolver { s =>
      s.declare(x.toVal)
      s.assertCnstr(Equals(double(one), two))
      assert(s.check(Simple) == Sat)
    }
  }

  test("Quantifiers the evaluator cannot decide are unknown") {
    // The evaluator checks quantifiers with the selected solver, here `eval` itself.
    val reporter = new RecordingReporter(Set())
    val s = loudSolver(reporter)
    val z = "z" :: IntegerType()
    s.assertCnstr(Forall(Seq(z), LessThan(z.toVariable, IntegerLiteral(100))))
    assert(s.check(Simple) == Unknown)
    assert(reporter.errors.exists(_.contains("Failed to evaluate forall")), reporter.errors)
  }

  test("Errors are not reported after an interrupt, until a reset") {
    val reporter = new RecordingReporter(Set())
    val s = loudSolver(reporter)
    s.interrupt()
    s.assertCnstr(Equals(Division(one, IntegerLiteral(0)), one))
    assert(s.check(Simple) == Unknown)
    assert(reporter.errors.isEmpty)
    s.reset()
    s.assertCnstr(Equals(Division(one, IntegerLiteral(0)), one))
    assert(s.check(Simple) == Unknown)
    assert(reporter.errors.size == 1)
  }

  test("Errors are logged with their trace in the solver debug section") {
    val reporter = new RecordingReporter(Set(DebugSectionSolver))
    val s = loudSolver(reporter)
    s.assertCnstr(Equals(Division(one, IntegerLiteral(0)), one))
    assert(s.check(Simple) == Unknown)
    assert(reporter.errors.isEmpty)
    assert(reporter.messages.exists(_.msg.toString.contains("Runtime error during evaluation")))
  }

  test("Freeing the solver drops its constraints") {
    val s = factory.getNewSolver()
    s.assertCnstr(BooleanLiteral(false))
    s.free()
    assert(s.check(Simple) == Sat)
  }
}
