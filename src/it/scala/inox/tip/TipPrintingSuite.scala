/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import org.scalatest._

class TipPrintingSuite extends FunSuite with ResourceUtils {
  import inox.trees._

  val ctx = TestContext.empty

  val files = resourceFiles("regression/tip/SAT", _.endsWith(".tip")).toList.map("SAT" -> _) ++
    resourceFiles("regression/tip/UNSAT", _.endsWith(".tip")).map("UNSAT" -> _)

  private def checkScript(syms: Symbols, expr: Expr): Unit = {
    for (fd <- syms.functions.values) {
      assert(fd.fullBody.getType(syms) != Untyped)
    }

    assert(expr.getType(syms) != Untyped)
  }

  for ((cat, file) <- files) {
    test(s"Parsing file $cat/${file.getName}") {
      for ((syms, expr) <- new Parser(file).parseScript) {
        checkScript(syms, expr)
      }
    }

    test(s"Re-printing file $cat/${file.getName}") {
      for ((syms, expr) <- new Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)

        val file = java.io.File.createTempFile("test-output", ".tip")
        val fw = new java.io.FileWriter(file, false)
        val printer = new Printer(program, fw)
        printer.printScript(expr)
        printer.emit(smtlib.trees.Commands.CheckSat())
        printer.free()

        val Seq((newSyms, newExpr)) = new Parser(file).parseScript
        file.delete()
        checkScript(newSyms, newExpr)
      }
    }
  }
}
