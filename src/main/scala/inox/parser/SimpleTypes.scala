package inox
package parser

trait SimpleTypes {

  sealed trait SimpleType

  final class Unknown private(private val identifier: Int) extends SimpleType {
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

  object SimpleTypes {
    case class UnitType() extends SimpleType
    case class BitVectorType(size: Int) extends SimpleType
    case class IntegerType() extends SimpleType
    case class StringType() extends SimpleType
    case class CharType() extends SimpleType
    case class RealType() extends SimpleType
    case class FunctionType(froms: Seq[SimpleType], to: SimpleType) extends SimpleType
    case class MapType(from: SimpleType, to: SimpleType) extends SimpleType
    case class SetType(elem: SimpleType) extends SimpleType
    case class BagType(elem: SimpleType) extends SimpleType
    case class TupleType(elems: Seq[SimpleType]) extends SimpleType
    case class ADTType(identifier: inox.Identifier, args: Seq[SimpleType]) extends SimpleType
    case class TypeParameter(identifier: inox.Identifier) extends SimpleType
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

    def hasInstance(tpe: SimpleType): Boolean
  }
  case object Comparable extends TypeClass {
    override val name = "Comparable"

    override def hasInstance(tpe: SimpleType) = {
      tpe == CharType() || Numeric.hasInstance(tpe)
    }
  }
  case object Numeric extends TypeClass {
    override val name = "Numeric"

    override def hasInstance(tpe: SimpleType) = {
      tpe == RealType() || Integral.hasInstance(tpe)
    }
  }
  case object Integral extends TypeClass {
    override val name = "Integral"

    override def hasInstance(tpe: SimpleType) = {
      tpe == IntegerType() || Bits.hasInstance(tpe)
    }
  }
  case object Bits extends TypeClass {
    override val name = "Bits"

    override def hasInstance(tpe: SimpleType) =
      tpe.isInstanceOf[BitVectorType]
  }
}