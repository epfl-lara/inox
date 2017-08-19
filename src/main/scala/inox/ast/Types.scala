/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package ast

trait Types { self: Trees =>

  trait Typed extends Printable {
    def getType(implicit s: Symbols): Type
    def isTyped(implicit s: Symbols): Boolean = getType != Untyped
  }

  protected trait CachingTyped extends Typed {
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

  object Int8Type extends BVType(8) {
    override def toString = "Int8Type"
  }
  object Int16Type extends BVType(16) {
    override def toString = "Int16Type"
  }
  object Int32Type extends BVType(32) {
    override def toString = "Int32Type"
  }
  object Int64Type extends BVType(64) {
    override def toString = "Int64Type"
  }

  case class TypeParameter(id: Identifier, flags: Set[Flag]) extends Type {
    def freshen = TypeParameter(id.freshen, flags)

    def isCovariant = flags contains Variance(true)
    def isContravariant = flags contains Variance(false)
    def isInvariant = !isCovariant && !isContravariant

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
  case class TupleType(bases: Seq[Type]) extends Type {
    val dimension: Int = bases.length
    require(dimension >= 2)
  }

  case class SetType(base: Type) extends Type
  case class BagType(base: Type) extends Type
  case class MapType(from: Type, to: Type) extends Type
  case class FunctionType(from: Seq[Type], to: Type) extends Type

  case class ADTType(id: Identifier, tps: Seq[Type]) extends Type {
    def lookupADT(implicit s: Symbols): Option[TypedADTDefinition] = s.lookupADT(id, tps)
    def getADT(implicit s: Symbols): TypedADTDefinition = s.getADT(id, tps)

    def getField(selector: Identifier)(implicit s: Symbols): Option[ValDef] = lookupADT match {
      case Some(tcons: TypedADTConstructor) =>
        tcons.fields.collectFirst { case vd @ ValDef(`selector`, _, _) => vd }
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

  object FirstOrderFunctionType {
    def unapply(tpe: FunctionType): Option[(Seq[Type], Type)] = tpe match {
      case FunctionType(from, to: FunctionType) =>
        val Some((toFrom, toTo)) = unapply(to)
        Some((from ++ toFrom, toTo))
      case FunctionType(from, to) =>
        Some(from -> to)
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

