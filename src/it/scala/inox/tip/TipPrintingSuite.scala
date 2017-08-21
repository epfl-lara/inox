/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import org.scalatest._

class TipPrintingSuite extends FunSuite with ResourceUtils {
  import inox.trees._

  val ctx = TestContext.empty

  val files = resourceFiles("regression/tip/SAT", _.endsWith(".tip")).toList.map("SAT" -> _) ++
    resourceFiles("regression/tip/UNSAT", _.endsWith(".tip")).map("UNSAT" -> _)

  private def checkScript(program: InoxProgram, expr: Expr): Unit = {
    import program._
    for (fd <- symbols.functions.values) {
      assert(symbols.isSubtypeOf(fd.fullBody.getType, fd.returnType))
    }

    assert(expr.isTyped)
  }

  for ((cat, file) <- files) {
    test(s"Parsing file $cat/${file.getName}") {
      for ((program, expr) <- new Parser(file).parseScript) {
        checkScript(program, expr)
      }
    }

    test(s"Re-printing file $cat/${file.getName}") {
      for ((program, expr) <- new Parser(file).parseScript) {
        val file = java.io.File.createTempFile("test-output", ".tip")
        val fw = new java.io.FileWriter(file, false)
        val printer = new Printer(program, ctx, fw)
        printer.printScript(expr)
        printer.emit(smtlib.trees.Commands.CheckSat())
        printer.free()

        val Seq((newProgram, newExpr)) = new Parser(file).parseScript
        file.delete()
        checkScript(newProgram, newExpr)
      }
    }
  }
}
