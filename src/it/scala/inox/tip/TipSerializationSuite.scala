/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package tip

import org.scalatest._

class TipSerializationSuite extends FunSuite with ResourceUtils {
  import inox.trees._

  val ctx = TestContext.empty

  val filesWithCat = resourceFiles("regression/tip", filter = _ endsWith ".tip", recursive = true).map { f =>
    f.getParentFile.getName -> f
  }

  for ((cat, file) <- filesWithCat) {
    test(s"Serializing/deserializing file $cat/${file.getName}") {
      val serializer = utils.Serializer(inox.trees)
      for ((program, expr) <- new Parser(file).parseScript) {
        val out = new java.io.ByteArrayOutputStream
        serializer.serializeSymbols(program.symbols, out)
        serializer.serialize(expr, out)

        val in = new java.io.ByteArrayInputStream(out.toByteArray)
        val newSymbols = serializer.deserializeSymbols(in)
        val newExpr = serializer.deserialize[Expr](in)

        assert(program.symbols == newSymbols)
        assert(expr == newExpr)
      }
    }
  }
}
