package inox
package parser
package elaboration

trait SimpleTypes { self: Trees =>

  object SimpleTypes {

    sealed abstract class Type
    case class UnitType() extends Type
    case class BooleanType() extends Type
    case class BitVectorType(size: Int) extends Type
    case class IntegerType() extends Type
    case class StringType() extends Type
    case class CharType() extends Type
    case class RealType() extends Type
    case class FunctionType(froms: Seq[Type], to: Type) extends Type
    case class MapType(from: Type, to: Type) extends Type
    case class SetType(elem: Type) extends Type
    case class BagType(elem: Type) extends Type
    case class TupleType(elems: Seq[Type]) extends Type
    case class ADTType(identifier: inox.Identifier, args: Seq[Type]) extends Type
    case class TypeParameter(identifier: inox.Identifier) extends Type

    final class Unknown private(private val identifier: Int) extends Type {
      override def equals(that: Any): Boolean =
        that.isInstanceOf[Unknown] && that.asInstanceOf[Unknown].identifier == identifier
    }

    object Unknown {
      private var next: Int = 0

      def fresh: Unknown = synchronized {
        val ret = next
        next += 1
        new Unknown(ret)
      }
    }

    def fromInox(tpe: trees.Type): Type = ???
    def toInox(tpe: Type): trees.Type = ???
  }
}