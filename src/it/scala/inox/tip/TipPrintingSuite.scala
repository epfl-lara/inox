/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import org.scalatest._

class TipPrintingSuite extends FunSuite with ResourceUtils {
  import inox.trees._

  val ctx = TestContext.empty

  val filesWithCat = resourceFiles("regression/tip/", filter = _ endsWith ".tip", recursive = true) map { f =>
    f.getParentFile.getName -> f
  }

  private def checkScript(program: InoxProgram, expr: Expr): Unit = {
    import program.symbols
    symbols.ensureWellFormed

    assert(expr.isTyped)
  }

  for ((cat, file) <- filesWithCat) {
    test(s"Parsing file $cat/${file.getName}") {
      for ((program, expr) <- new Parser(file).parseScript) {
        checkScript(program, expr)
      }
    }

    test(s"Re-printing file $cat/${file.getName}") {
      for ((program, expr) <- new Parser(file).parseScript) {
        val file = java.io.File.createTempFile("test-output", ".tip")
        file.deleteOnExit()
        val fw = new java.io.FileWriter(file, false)
        val printer = new Printer(program, ctx, fw)
        printer.printScript(expr)
        printer.emit(smtlib.trees.Commands.CheckSat())
        printer.free()

        val Seq((newProgram, newExpr)) = new Parser(file).parseScript
        checkScript(newProgram, newExpr)
      }
    }
  }
}
