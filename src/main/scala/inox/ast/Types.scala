/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait Types { self: Trees =>

  trait Typed extends Printable {
    def getType(implicit s: Symbols): Type
    def isTyped(implicit s: Symbols): Boolean = getType != Untyped
  }

  private[ast] trait CachingTyped extends Typed {
    private var lastSymbols: Symbols = null
    private var lastType: Type = null

    final def getType(implicit s: Symbols): Type =
      if (s eq lastSymbols) lastType else {
        val tpe = computeType
        lastSymbols = s
        lastType = tpe
        tpe
      }

    protected def computeType(implicit s: Symbols): Type
  }

  abstract class Type extends Tree with Typed {
    def getType(implicit s: Symbols): Type = this

    // Checks whether the subtypes of this type contain Untyped,
    // and if so sets this to Untyped.
    // Assumes the subtypes are correctly formed, so it does not descend 
    // deep into the TypeTree.
    def unveilUntyped: Type = this match {
      case NAryType(tps, _) =>
        if (tps contains Untyped) Untyped else this
    }
  }

  case object Untyped     extends Type
  case object BooleanType extends Type
  case object UnitType    extends Type
  case object CharType    extends Type
  case object IntegerType extends Type
  case object RealType    extends Type
  case object StringType  extends Type

  case class BVType(size: Int) extends Type
  object Int32Type extends BVType(32) {
    override def toString = "Int32Type"
  }

  class TypeParameter private (name: String) extends Type {
    val id = FreshIdentifier(name)
    def freshen = new TypeParameter(name)

    override def equals(that: Any) = that match {
      case TypeParameter(id) => this.id == id
      case _ => false
    }

    override def hashCode = id.hashCode
  }

  object TypeParameter {
    def unapply(tp: TypeParameter): Option[Identifier] = Some(tp.id)
    def fresh(name: String) = new TypeParameter(name)
  }

  /* 
   * If you are not sure about the requirement, 
   * you should use tupleTypeWrap in purescala.Constructors
   */
  case class TupleType(bases: Seq[Type]) extends Type {
    val dimension: Int = bases.length
    require(dimension >= 2)
  }

  case class SetType(base: Type) extends Type
  case class BagType(base: Type) extends Type
  case class MapType(from: Type, to: Type) extends Type
  case class FunctionType(from: Seq[Type], to: Type) extends Type

  case class ClassType(id: Identifier, tps: Seq[Type]) extends Type {
    def lookupClass(implicit s: Symbols): Option[TypedClassDef] = s.lookupClass(id, tps)
    def tcd(implicit s: Symbols): TypedClassDef = s.getClass(id, tps)
  }

  object NAryType extends TreeExtractor {
    val trees: Types.this.type = Types.this

    type SubTree = Type

    def unapply(t: Type): Option[(Seq[Type], Seq[Type] => Type)] = t match {
      case ClassType(ccd, ts) => Some((ts, ts => ClassType(ccd, ts)))
      case TupleType(ts) => Some((ts, TupleType))
      case SetType(t) => Some((Seq(t), ts => SetType(ts.head)))
      case BagType(t) => Some((Seq(t), ts => BagType(ts.head)))
      case MapType(from,to) => Some((Seq(from, to), t => MapType(t(0), t(1))))
      case FunctionType(fts, tt) => Some((tt +: fts, ts => FunctionType(ts.tail.toList, ts.head)))
      /* nullary types */
      case t => Some(Nil, _ => t)
    }
  }

  object FirstOrderFunctionType {
    def unapply(tpe: Type): Option[(Seq[Type], Type)] = tpe match {
      case FunctionType(from, to) =>
        unapply(to).map(p => (from ++ p._1) -> p._2) orElse Some(from -> to)
      case _ => None
    }
  }
}
