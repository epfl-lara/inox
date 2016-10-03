/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import org.scalatest._
import org.scalatest.concurrent._

import solvers._
import utils._

class TIPTestSuite extends InoxTestSuite with ResourceUtils {

  val tipDir = "tip-benchmarks/benchmarks"

  def makeTests(base: String) = {
    val files = resourceFiles(s"$tipDir/$base")

    if (files.isEmpty) {
      ignore(s"tip-benchmarks: $base directory not found (missing git submodule?") {_ => ()}
    } else {
      for (file <- files) {
        test(s"Verifying tip-benchmarks/$base") { ctx =>
          val (syms, clause) = parsers.TIPParser.parse(file)
          val program = InoxProgram(ctx, syms)

          assert(SimpleSolverAPI(SolverFactory.default(program)).solveSAT(clause).isSAT)
        }
      }
    }
  }

  makeTests("grammars")
  makeTests("isaplanner")
  makeTests("prod")
  makeTests("tip2015")
}
