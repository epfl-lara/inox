/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import solvers._
import org.scalatest._

class TIPTestSuite extends FunSuite with ResourceUtils {

  val ctx = TestContext.empty

  for (file <- resourceFiles("regression/tip/SAT", _.endsWith(".tip"))) {
    test(s"SAT - ${file.getName}") {
      for ((syms, expr) <- new tip.Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(expr).isSAT)
      }
    }
  }

  for (file <- resourceFiles("regression/tip/UNSAT", _.endsWith(".tip"))) {
    test(s"UNSAT - ${file.getName}") {
      for ((syms, expr) <- new tip.Parser(file).parseScript) {
        val program = InoxProgram(ctx, syms)
        assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(expr).isUNSAT)
      }
    }
  }
}
