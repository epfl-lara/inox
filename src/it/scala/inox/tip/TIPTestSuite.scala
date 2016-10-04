/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import org.scalatest._

import solvers._
import utils._

class TIPTestSuite extends FunSuite with ResourceUtils {

  val tipDir = "tip-benchmarks/benchmarks"

  def makeTests(base: String) = {
    val files = resourceFiles(s"$tipDir/$base")

    if (files.isEmpty) {
      ignore(s"tip-benchmarks: $base directory not found (missing git submodule?") {}
    } else {
      val baseFile = new java.io.File(getClass.getResource(s"/$tipDir").getPath)
      for (file <- files) {
        val path = baseFile.toURI.relativize(file.toURI).getPath

        test(s"Parsing tip-benchmarks/$path") {
          parsers.TIPParser.parse(file)
        }
      }
    }
  }

  makeTests("grammars")
  makeTests("isaplanner")
  makeTests("prod")
  makeTests("tip2015")
}
