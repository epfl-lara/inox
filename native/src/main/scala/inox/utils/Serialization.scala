// Scala Native overlay of src/main/scala/inox/utils/Serialization.scala.
// The binary serializer rebuilds trees through Java reflection
// (Class.forName, getConstructors), which Scala Native does not provide, so
// the native command line only reads TIP input.

package inox
package utils

trait Serializer {
  val trees: ast.Trees
  def deserialize[T](in: java.io.InputStream): T =
    throw new UnsupportedOperationException("the binary format is not supported by the native build of Inox")
}

object Serializer {
  def apply(t: ast.Trees, serializeProducts: Boolean = false): Serializer { val trees: t.type } =
    new Serializer { val trees: t.type = t }
}
