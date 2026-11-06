/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package smtlib3

import org.scalatest.funsuite.AnyFunSuite

import java.io.{StringReader, StringWriter}

/** Prints the TIP regression benchmarks in SMT-LIB 3, and parses them back. */
class SMTLIB3PrintingSuite extends AnyFunSuite with ResourceUtils {
  import inox.trees._

  val ctx = TestContext.empty

  val filesWithCat = resourceFiles("regression/tip/", filter = _ `endsWith` ".tip", recursive = true) map { f =>
    f.getParentFile.getName -> f
  }

  private def print(program: InoxProgram, expr: Expr): String = {
    val writer = new StringWriter
    val printer = new Printer(program, ctx, writer)
    printer.printScript(expr)
    printer.emit("(check-sat)\n")
    printer.free()
    writer.toString
  }

  /** The commands of `script`, without the suffixes that make symbols unique (`x!3`), and in
    * sorted order since independent datatypes are declared in any order. */
  private def canonical(script: String): Seq[String] =
    script.linesIterator.map(_.replaceAll("(![0-9]+)+", "")).filter(_.trim.nonEmpty).toSeq.sorted


  private def reparse(program: InoxProgram, expr: Expr): (InoxProgram, Expr, String) = {
    val script = print(program, expr)
    val Seq((newProgram, newExpr)) = try Parser(new StringReader(script)).parseScript catch {
      case e: tip.MissformedTIPException => fail(s"couldn't parse the printed script\n$script", e)
    }: @unchecked

    import newProgram.symbols.{given, _}
    withClue(script) {
      symbols.ensureWellFormed
      assert(newExpr.isTyped)
    }
    (newProgram, newExpr, script)
  }

  for ((cat, file) <- filesWithCat) {
    test(s"Printing file $cat/${file.getName} in SMT-LIB 3") {
      for ((program, expr) <- tip.Parser(file).parseScript) {
        val (newProgram, newExpr, script) = reparse(program, expr)
        val (lastProgram, lastExpr, reprinted) = reparse(newProgram, newExpr)
        // some trees are printed as combinations of other trees, so the first printing may differ
        if (canonical(reprinted) != canonical(script)) {
          val (_, _, last) = reparse(lastProgram, lastExpr)
          assert(canonical(last) == canonical(reprinted), s"printing isn't a fixpoint:\n$reprinted\nbecame\n$last")
        }
      }
    }
  }

  // The printed benchmarks keep their status (except for those that need specific options, see TipTestSuite)
  private val skipped = Set("ForallAssoc.scala-0.tip", "LambdaEquality2.scala-1.tip", "QuickSortFilter.scala-1.tip")

  for ((cat, file) <- filesWithCat if (cat == "SAT" || cat == "UNSAT") && !skipped(file.getName)) {
    test(s"Solving file $cat/${file.getName} printed in SMT-LIB 3") {
      val solver =
        if (solvers.SolverFactory.hasNativeZ3) "nativez3"
        else if (solvers.SolverFactory.hasZ3) "smt-z3"
        else cancel("these checks need Z3")
      val solverCtx = TestContext(Options(Seq(
        optSelectedSolvers(Set(solver)),
        solvers.optCheckModels(true),
      )))
      for ((program, expr) <- tip.Parser(file).parseScript) {
        val (newProgram, newExpr, script) = reparse(program, expr)
        val res = solvers.SimpleSolverAPI(newProgram.getSolver(solverCtx)).solveSAT(newExpr)
        assert(if (cat == "SAT") res.isSAT else res.isUNSAT, s"$res for\n$script")
      }
    }
  }
}
