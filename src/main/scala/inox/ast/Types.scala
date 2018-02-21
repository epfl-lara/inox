/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait Types { self: Trees =>

  trait Typed extends Printable {
    def getType(implicit s: Symbols): Type
    def isTyped(implicit s: Symbols): Boolean = getType != Untyped
  }

  protected trait CachingTyped extends Typed {
    private[this] var cache: (Symbols, Type) = (null, null)

    final def getType(implicit s: Symbols): Type = {
      val (symbols, tpe) = cache
      if (s eq symbols) tpe else {
        val tpe = computeType
        cache = s -> tpe
        tpe
      }
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

  case object Untyped extends Type

  case class BooleanType() extends Type
  case class UnitType()    extends Type
  case class CharType()    extends Type
  case class IntegerType() extends Type
  case class RealType()    extends Type
  case class StringType()  extends Type

  sealed case class BVType(size: Int) extends Type {
    override def toString: String = size match {
      case 8  => "Int8Type"
      case 16 => "Int16Type"
      case 32 => "Int32Type"
      case 64 => "Int64Type"
      case _ => super.toString
    }
  }

  sealed abstract class BVTypeExtractor(size: Int) {
    def apply(): BVType = BVType(size)
    def unapply(tpe: BVType): Boolean = tpe.size == size
  }

  object Int8Type  extends BVTypeExtractor(8)
  object Int16Type extends BVTypeExtractor(16)
  object Int32Type extends BVTypeExtractor(32)
  object Int64Type extends BVTypeExtractor(64)

  sealed case class TypeParameter(id: Identifier, flags: Set[Flag]) extends Type {
    def freshen = TypeParameter(id.freshen, flags)

    override def equals(that: Any) = that match {
      case tp: TypeParameter => id == tp.id
      case _ => false
    }

    override def hashCode = id.hashCode
  }

  object TypeParameter {
    def fresh(name: String) = TypeParameter(FreshIdentifier(name), Set.empty)
  }

  /* 
   * If you are not sure about the requirement, 
   * you should use tupleTypeWrap in purescala.Constructors
   */
  sealed case class TupleType(bases: Seq[Type]) extends Type {
    val dimension: Int = bases.length
    require(dimension >= 2)
  }

  sealed case class SetType(base: Type) extends Type
  sealed case class BagType(base: Type) extends Type
  sealed case class MapType(from: Type, to: Type) extends Type
  sealed case class FunctionType(from: Seq[Type], to: Type) extends Type

  sealed case class ADTType(id: Identifier, tps: Seq[Type]) extends Type {
    def lookupSort(implicit s: Symbols): Option[TypedADTSort] = s.lookupSort(id, tps)
    def getSort(implicit s: Symbols): TypedADTSort = s.getSort(id, tps)

    def getField(selector: Identifier)(implicit s: Symbols): Option[ValDef] = lookupSort match {
      case Some(tsort: TypedADTSort) =>
        tsort.constructors.flatMap(_.fields).collectFirst {
          case vd @ ValDef(`selector`, _, _) => vd
        }
      case _ => None
    }
  }

  /** NAryType extractor to extract any Type in a consistent way.
    *
    * @see [[Extractors.Operator]] about why we can't have nice(r) things
    */
  object NAryType extends {
    protected val s: self.type = self
    protected val t: self.type = self
  } with TreeExtractor {
    type Source = Type
    type Target = Type

    def unapply(t: Type): Option[(Seq[Type], Seq[Type] => Type)] = {
      val (ids, tps, flags, recons) = deconstructor.deconstruct(t)
      Some((tps, tps => recons(ids, tps, flags)))
    }
  }

  object typeOps extends {
    protected val sourceTrees: self.type = self
    protected val targetTrees: self.type = self
  } with GenTreeOps {
    type Source = self.Type
    type Target = self.Type
    lazy val Deconstructor = NAryType
  }
}

