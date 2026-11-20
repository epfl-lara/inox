/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

import java.io.File

/** The SMT-LIB text of a query doesn't depend on the identifiers that other queries allocate.
  *
  * Identifiers take their ids, and thus their hash codes, from a global counter, so the queries
  * that run in parallel see different ids for the same symbols. The SMT symbols are numbered per
  * target, and the unrolling instantiates the items of its templates in the order in which they
  * were found rather than in hash order, so the same query gives the same text either way. */
class DeterministicEncodingSuite extends AnyFunSuite {
  import inox.trees._
  import inox.trees.dsl._
  import SolverResponses._

  private def session(program: InoxProgram, run: Int)(query: Expr): String = {
    val source = s"DeterministicEncodingSuite-$run-${System.nanoTime}.scala"
    val reporter = new DefaultReporter(Set(smtlib.DebugSectionSMT))
    val ctx = Context(reporter, new utils.InterruptManager(reporter),
      Options(Seq(optSelectedSolvers(Set("smt-z3")), Main.optFiles(Seq(new File(source))))))
    def outputs = Option(new File("smt-sessions").listFiles()).toSeq.flatten.filter(_.getName.contains(source))
    try {
      val s = program.getSolver(ctx).getNewSolver()
      s.assertCnstr(query)
      assert(s.check(Simple) == Sat)
      s.free()
      outputs.map(f => scala.io.Source.fromFile(f).mkString).mkString("\n")
        .linesIterator.filterNot(_.startsWith(";")).mkString("\n")
    } finally outputs.foreach(_.delete())
  }

  val fID = FreshIdentifier("f")
  // f(x) = if (x <= 0) 1 else f(x - 1) + ... + f(x - 6), whose calls share a blocker
  val f = mkFunDef(fID)() { _ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
      if_ (x <= E(BigInt(0))) {
        E(BigInt(1))
      } else_ {
        (1 to 6).map(i => E(fID)(x - E(BigInt(i)))).reduce(_ + _)
      }
    })
  }

  val hID = FreshIdentifier("h")
  // h(g, x) = g(x) + ... + g(x + 5), whose applications share a blocker
  val h = mkFunDef(hID)() { _ => (
    Seq("g" :: (IntegerType() =>: IntegerType()), "x" :: IntegerType()), IntegerType(), { case Seq(g, x) =>
      (0 to 5).map(i => g(x + E(BigInt(i)))).reduce(_ + _)
    })
  }

  val program = InoxProgram(NoSymbols.withFunctions(Seq(f, h)))

  test("The same query gives the same SMT-LIB text whatever identifiers were allocated before") {
    val y = Variable.fresh("y", IntegerType())
    val g = Variable.fresh("g", IntegerType() =>: IntegerType())
    val query = And(Equals(y, E(BigInt(2))), Equals(E(hID)(g, y), E(fID)(y)))

    val first = session(program, 1)(query)
    assert(first.nonEmpty)
    // shifts the ids of the identifiers that the next runs allocate
    for ((shift, run) <- Seq(1000, 777).zipWithIndex) {
      for (_ <- 1 to shift) FreshIdentifier("shift")
      assert(session(program, run + 2)(query) == first)
    }
  }
}
