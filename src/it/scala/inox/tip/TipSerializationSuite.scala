/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package tip

import org.scalatest.funspec.AnyFunSpec

class TipSerializationSuite extends AnyFunSpec with ResourceUtils {
  import inox.trees._

  val ctx = TestContext.empty

  val filesWithCat = resourceFiles("regression/tip", filter = _ endsWith ".tip", recursive = true).map { f =>
    f.getParentFile.getName -> f
  }

  // We have to be careful what we unregister as not all `classSerializers` are case classes
  class ProductSerializer(trees: ast.Trees) extends  utils.InoxSerializer(trees, serializeProducts = true) {
    override protected def classSerializers =
      super.classSerializers.filterNot(p => 30 <= p._2.id && p._2.id <= 40)
  }

  def checkSerializer(
    serializer: utils.Serializer { val trees: inox.trees.type },
    program: Program { val trees: inox.trees.type },
    expr: Expr
  ) = {
    import serializer._

    val out = new java.io.ByteArrayOutputStream
    serializer.serialize(program.symbols, out)
    serializer.serialize(expr, out)

    val outBytes = out.toByteArray
    val in = new java.io.ByteArrayInputStream(outBytes)
    val newSymbols = serializer.deserialize[Symbols](in)
    val newExpr = serializer.deserialize[Expr](in)

    assert(program.symbols == newSymbols)
    assert(expr == newExpr)

    val out2 = new java.io.ByteArrayOutputStream
    serializer.serialize(newSymbols, out2)
    serializer.serialize(newExpr, out2)
    val out2Bytes = out2.toByteArray
    assert(java.util.Arrays.equals(outBytes, out2Bytes))
  }

  for ((cat, file) <- filesWithCat) {
    describe(s"Serializing/deserializing file $cat/${file.getName}") {
      it("with registered classes") {
        val serializer = utils.Serializer(inox.trees)
        for ((program, expr) <- Parser(file).parseScript) checkSerializer(serializer, program, expr)
      }

      it("with unregistered classes") {
        val serializer = new ProductSerializer(inox.trees)
          .asInstanceOf[utils.Serializer { val trees: inox.trees.type }]
        for ((program, expr) <- Parser(file).parseScript) checkSerializer(serializer, program, expr)
      }
    }
  }
}
