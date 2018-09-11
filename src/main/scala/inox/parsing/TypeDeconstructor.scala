/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package parsing

trait TypeDeconstructors extends IRs {

  trait TypeDeconstructor {

    import TypeIR._

    object BVType {
      def apply(signed: Boolean, size: Int): String = {
        require(size > 0)

        if (signed) "Int" + size
        else "UInt" + size
      }

      def unapply(name: String): Option[(Boolean,Int)] = {
        if (name.startsWith("Int")) {
          scala.util.Try(name.drop(3).toInt).toOption.filter(_ > 0).map(i => (true,i))
        } else if (name.startsWith("UInt")) {
          scala.util.Try(name.drop(4).toInt).toOption.filter(_ > 0).map(i => (false,i))
        } else {
          None
        }
      }
    }

    lazy val basic: Map[Value, trees.Type] = Seq(
      "Boolean" -> trees.BooleanType(),
      "BigInt"  -> trees.IntegerType(),
      "Char"    -> trees.CharType(),
      "Int"     -> trees.Int32Type(),
      "Real"    -> trees.RealType(),
      "String"  -> trees.StringType(),
      "Unit"    -> trees.UnitType()).map({ case (n, v) => Name(n) -> v }).toMap
  }
}
