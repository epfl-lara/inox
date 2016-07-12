/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Common._
import Expressions._
import Definitions._
import TypeOps._

trait Types { self: Trees =>

  trait Typed extends Printable {
    def getType(implicit p: Program): Type
    def isTyped(implicit p: Program): Boolean = getType != Untyped
  }

  private[trees] trait CachingTyped extends Typed {
    private var lastProgram: Program = null
    private var lastType: Type = null

    final def getType(implicit p: Program): Type =
      if (p eq lastProgram) lastType else {
        val tpe = computeType
        lastProgram = p
        lastType = tpe
        tpe
      }

    protected def computeType(implicit p: Program): Type
  }

  abstract class Type extends Tree with Typed {
    def getType(implicit p: Program): Type = this

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
  case object Int32Type extends BVType(32)

  class TypeParameter private (name: String) extends Type {
    val id = FreshIdentifier(name, this)
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
    def lookupClass(implicit p: Program): Option[ClassDef] = p.lookupClass(id, tps)
  }

  object NAryType extends TreeExtractor[Type] {
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
