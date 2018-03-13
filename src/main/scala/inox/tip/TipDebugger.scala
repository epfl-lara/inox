/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import utils._
import solvers._

trait TipDebugger extends Solver {
  import program._
  import program.trees._
  import SolverResponses._

  protected val encoder: ast.ProgramTransformer {
    val sourceProgram: program.type
    val targetProgram: Program { val trees: inox.trees.type }
  }

  implicit val debugSection: DebugSection

  abstract override def free(): Unit = {
    super.free()
    debugOut.foreach(_.free())
  }

  protected lazy val debugOut: Option[tip.Printer] = {
    if (context.reporter.isDebugEnabled) {
      val files = context.options.findOptionOrDefault(Main.optFiles)
      if (files.nonEmpty && files.forall(_.getName.endsWith(".tip"))) {
        // don't output TIP when running on a TIP benchmark
        None
      } else {
        val file = files.headOption.map(_.getName).getOrElse("NA")
        val n = DebugFileNumbers.next(file)
        val fileName = s"tip-sessions/$file-$n.tip"

        val javaFile = new java.io.File(fileName)
        javaFile.getParentFile.mkdirs()

        context.reporter.debug(s"Outputting tip session into $fileName")
        val fw = new java.io.FileWriter(javaFile, false)
        Some(new tip.Printer(encoder.targetProgram, context, fw))
      }
    } else {
      None
    }
  }

  abstract override def assertCnstr(expr: Expr): Unit = {
    debugOut.foreach { o => o.printScript(encoder.encode(expr)) }
    super.assertCnstr(expr)
  }

  abstract override def check(config: CheckConfiguration): config.Response[Model, Assumptions] = {
    debugOut.foreach { o => o.emit(_root_.smtlib.trees.Commands.CheckSat()) }
    super.check(config)
  }

  abstract override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
    debugOut.foreach { o => o.emit("; check-assumptions required here, but not part of tip standard") }
    super.checkAssumptions(config)(assumptions)
  }
}

// Unique numbers
private[tip] object DebugFileNumbers extends UniqueCounter[String]
