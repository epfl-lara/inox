package inox
package parser

trait SimpleTypes {

  object SimpleTypes {

    sealed abstract class Type

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
    case class UnitType() extends Type
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
  }

  import SimpleTypes._

  sealed abstract class TypeClass {
    val name: String

    def &(that: TypeClass) = (this, that) match {
      case (Bits, _) => Bits
      case (_, Bits) => Bits
      case (Integral, _) => Integral
      case (_, Integral) => Integral
      case (Numeric, _) => Numeric
      case (_, Numeric) => Numeric
      case _ => Comparable
    }

    def hasInstance(tpe: Type): Boolean
  }
  case object Comparable extends TypeClass {
    override val name = "Comparable"

    override def hasInstance(tpe: Type) = {
      tpe == CharType() || Numeric.hasInstance(tpe)
    }
  }
  case object Numeric extends TypeClass {
    override val name = "Numeric"

    override def hasInstance(tpe: Type) = {
      tpe == RealType() || Integral.hasInstance(tpe)
    }
  }
  case object Integral extends TypeClass {
    override val name = "Integral"

    override def hasInstance(tpe: Type) = {
      tpe == IntegerType() || Bits.hasInstance(tpe)
    }
  }
  case object Bits extends TypeClass {
    override val name = "Bits"

    override def hasInstance(tpe: Type) =
      tpe.isInstanceOf[BitVectorType]
  }
}