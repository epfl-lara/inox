/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

import java.io.File

/** With the `smt` and `tip` debug sections, solvers write their sessions to `smt-sessions/` and `tip-sessions/`. */
class DebugSessionsSuite extends AnyFunSuite {
  import inox.trees._
  import SolverResponses._

  class QuietReporter(sections: Set[DebugSection]) extends DefaultReporter(sections) {
    var warnings = 0
    override def doEmit(msg: Message): Unit = if (msg.severity == WARNING) warnings += 1
  }

  private def withSessions(name: String, sections: Set[DebugSection])(body: (Context, QuietReporter) => Unit): Seq[String] = {
    val source = s"DebugSessionsSuite-$name-${System.nanoTime}.scala"
    val reporter = new QuietReporter(sections)
    val ctx = Context(reporter, new utils.InterruptManager(reporter),
      Options(Seq(optSelectedSolvers(Set("smt-z3")), Main.optFiles(Seq(new File(source))))))
    def outputs = Seq(new File("smt-sessions"), new File("tip-sessions"))
      .flatMap(dir => Option(dir.listFiles()).toSeq.flatten)
      .filter(_.getName.contains(source))
    try {
      body(ctx, reporter)
      outputs.map(f => scala.io.Source.fromFile(f).mkString)
    } finally outputs.foreach(_.delete())
  }

  val fid = FreshIdentifier("inc")
  val x = ValDef.fresh("x", IntegerType())
  val inc = new FunDef(fid, Seq(), Seq(x), IntegerType(), Plus(x.toVariable, IntegerLiteral(1)), Seq())
  val program = InoxProgram(NoSymbols.withFunctions(Seq(inc)))
  val y = Variable.fresh("y", IntegerType())

  test("SMT-LIB and TIP sessions") {
    val sessions = withSessions("both", Set(smtlib.DebugSectionSMT, tip.DebugSectionTip)) { (ctx, _) =>
      val s = program.getSolver(ctx).getNewSolver()
      s.assertCnstr(Equals(FunctionInvocation(fid, Seq(), Seq(y)), IntegerLiteral(3)))
      assert(s.check(Model).isSAT)
      val p = Variable.fresh("p", BooleanType())
      s.assertCnstr(Implies(p, GreaterThan(y, IntegerLiteral(0))))
      assert(s.checkAssumptions(Simple)(Set(p)) == Sat)
      s.free()
    }
    val (smt, tipSessions) = sessions.partition(_.contains("; Options:"))
    assert(smt.nonEmpty && smt.forall(_.contains("check-sat")))
    assert(tipSessions.size == 1)
    assert(tipSessions.head.contains("check-sat") && tipSessions.head.contains("check-assumptions"))
  }

  test("TIP sessions skip dependent types and warn once") {
    val sessions = withSessions("dependent", Set(tip.DebugSectionTip)) { (ctx, reporter) =>
      val s = program.getSolver(ctx).getNewSolver()
      val r = ValDef.fresh("r", IntegerType())
      val pos = Variable.fresh("pos", RefinementType(r, GreaterThan(r.toVariable, IntegerLiteral(0))))
      s.assertCnstr(Equals(pos, y))
      s.assertCnstr(GreaterThan(y, IntegerLiteral(0)))
      s.assertCnstr(Equals(pos, IntegerLiteral(2)))
      assert(s.check(Simple) == Sat)
      s.free()
      assert(reporter.warnings == 1)
    }
    assert(sessions.size == 1)
    assert(sessions.head.contains("(assert (> y"))
    assert(!sessions.head.contains("pos"))
  }
}
