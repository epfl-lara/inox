package inox
package parser
package elaboration

trait SimpleTypes { self: Trees =>

  object SimpleTypes {

    sealed abstract class Type {
      def contains(unknown: Unknown): Boolean = this match {
        case other: Unknown => unknown == other
        case FunctionType(froms, to) => froms.exists(_.contains(unknown)) || to.contains(unknown)
        case MapType(from, to) => from.contains(unknown) || to.contains(unknown)
        case SetType(elem) => elem.contains(unknown)
        case BagType(elem) => elem.contains(unknown)
        case TupleType(elems) => elems.exists(_.contains(unknown))
        case ADTType(_, args) => args.exists(_.contains(unknown))
        case _ => false
      }

      def unknowns: Set[Unknown] = this match {
        case unknown: Unknown => Set(unknown)
        case FunctionType(froms, to) => froms.map(_.unknowns).fold(to.unknowns)(_ union _)
        case MapType(from, to) => from.unknowns union to.unknowns
        case SetType(elem) => elem.unknowns
        case BagType(elem) => elem.unknowns
        case TupleType(elems) => elems.map(_.unknowns).fold(Set[Unknown]())(_ union _)
        case ADTType(_, args) => args.map(_.unknowns).fold(Set[Unknown]())(_ union _)
        case _ => Set()
      }

      def replaceTypeParams(mapping: Map[inox.Identifier, Type]): Type = this match {
        case TypeParameter(id) => mapping.getOrElse(id, this)
        case FunctionType(froms, to) => FunctionType(froms.map(_.replaceTypeParams(mapping)), to.replaceTypeParams(mapping))
        case MapType(from, to) => MapType(from.replaceTypeParams(mapping), to.replaceTypeParams(mapping))
        case SetType(elem) => SetType(elem.replaceTypeParams(mapping))
        case BagType(elem) => BagType(elem.replaceTypeParams(mapping))
        case TupleType(elems) => TupleType(elems.map(_.replaceTypeParams(mapping)))
        case ADTType(id, elems) => ADTType(id, elems.map(_.replaceTypeParams(mapping)))
        case _ => this
      }
    }
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
      override def hashCode(): Int = identifier
    }

    object Unknown {
      private var next: Int = 0

      def fresh: Unknown = synchronized {
        val ret = next
        next += 1
        new Unknown(ret)
      }
    }

    def fromInox(tpe: trees.Type): Option[Type] = tpe match {
      case trees.Untyped => None
      case trees.BooleanType() => Some(BooleanType())
      case trees.UnitType() => Some(UnitType())
      case trees.CharType() => Some(CharType())
      case trees.IntegerType() => Some(IntegerType())
      case trees.RealType() => Some(RealType())
      case trees.StringType() => Some(StringType())
      case trees.BVType(size) => Some(BitVectorType(size))
      case trees.TypeParameter(id, _) => Some(TypeParameter(id))
      case trees.TupleType(ts) => ts.foldLeft(Option(Seq[Type]())) {
        case (acc, t) => acc.flatMap(xs => fromInox(t).map(x => xs :+ x))
      }.map(TupleType(_))
      case trees.SetType(t) => fromInox(t).map(SetType(_))
      case trees.BagType(t) => fromInox(t).map(BagType(_))
      case trees.MapType(f, t) => fromInox(f).flatMap(sf => fromInox(t).map(st => MapType(sf, st)))
      case trees.FunctionType(fs, t) => fs.foldLeft(Option(Seq[Type]())) {
        case (acc, f) => acc.flatMap(xs => fromInox(f).map(x => xs :+ x))
      }.flatMap(sfs => fromInox(t).map(st => FunctionType(sfs, st)))
      case trees.ADTType(id, args) => args.foldLeft(Option(Seq[Type]())) {
        case (acc, f) => acc.flatMap(xs => fromInox(f).map(x => xs :+ x))
      }.map(ADTType(id, _))
      case trees.PiType(vds, t) => vds.foldLeft(Option(Seq[Type]())) {
        case (acc, vd) => acc.flatMap(xs => fromInox(vd.tpe).map(x => xs :+ x))
      }.flatMap(sfs => fromInox(t).map(st => FunctionType(sfs, st)))
      case trees.SigmaType(vds, t) => vds.foldLeft(Option(Seq[Type]())) {
        case (acc, vd) => acc.flatMap(xs => fromInox(vd.tpe).map(x => xs :+ x))
      }.flatMap(sfs => fromInox(t).map(st => TupleType(sfs :+ st)))
      case trees.RefinementType(vd, _) => fromInox(vd.tpe)
    }

    def toInox(tpe: Type): trees.Type = tpe match {
      case u: Unknown => throw new IllegalArgumentException("Unexpected Unknown.")
      case UnitType() => trees.UnitType()
      case BooleanType() => trees.BooleanType()
      case BitVectorType(size) => trees.BVType(size)
      case IntegerType() => trees.IntegerType()
      case StringType() => trees.StringType()
      case CharType() => trees.CharType()
      case RealType() => trees.RealType()
      case FunctionType(froms, to) => trees.FunctionType(froms.map(toInox), toInox(to))
      case MapType(from, to) => trees.MapType(toInox(from), toInox(to))
      case SetType(elem) => trees.SetType(toInox(elem))
      case BagType(elem) => trees.BagType(toInox(elem))
      case TupleType(elems) => trees.TupleType(elems.map(toInox))
      case ADTType(id, args) => trees.ADTType(id, args.map(toInox))
      case TypeParameter(id) => trees.TypeParameter(id, Seq())
    }
  }
}