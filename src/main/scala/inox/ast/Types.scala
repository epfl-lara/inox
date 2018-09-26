/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import scala.collection.mutable.{Map => MutableMap}

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

  /* Widens a type into it's narest outer Inox type.
   * This is an override point for more complex type systems that provide (for example)
   * type parameter bounds that would not be compatible with Inox type checking. */
  protected def widen(tpe: Type): Type = tpe

  protected def unveilUntyped(tpe: Type): Type = {
    val NAryType(tps, _) = tpe
    if (tps exists (_ == Untyped)) Untyped else tpe
  }

  abstract class Type extends Tree with Typed {
    private[this] var simple: Boolean = false
    private[this] var cache: (Symbols, Type) = (null, null)

    private def setSimple(): this.type = { simple = true; this }

    final def getType(implicit s: Symbols): Type = {
      if (simple) this else {
        val (symbols, tpe) = cache
        if (s eq symbols) tpe else {
          val tpe = computeType
          cache = s -> tpe.setSimple()
          tpe
        }
      }
    }

    protected def computeType(implicit s: Symbols): Type = {
      val NAryType(tps, recons) = this
      unveilUntyped(widen(recons(tps.map(_.getType))))
    }
  }

  case object Untyped extends Type

  case class BooleanType() extends Type
  case class UnitType()    extends Type
  case class CharType()    extends Type
  case class IntegerType() extends Type
  case class RealType()    extends Type
  case class StringType()  extends Type

  sealed case class BVType(signed: Boolean, size: Int) extends Type

  sealed abstract class BVTypeExtractor(signed: Boolean, size: Int) {
    def apply(): BVType = BVType(signed, size)
    def unapply(tpe: BVType): Boolean = tpe.signed == signed && tpe.size == size
  }

  object Int8Type  extends BVTypeExtractor(true, 8)
  object Int16Type extends BVTypeExtractor(true, 16)
  object Int32Type extends BVTypeExtractor(true, 32)
  object Int64Type extends BVTypeExtractor(true, 64)

  sealed case class TypeParameter(id: Identifier, flags: Seq[Flag]) extends Type {
    def freshen = TypeParameter(id.freshen, flags)

    override def equals(that: Any) = that match {
      case tp: TypeParameter => id == tp.id
      case _ => false
    }

    override def hashCode = id.hashCode
  }

  object TypeParameter {
    def fresh(name: String, flags: Seq[Flag] = Seq.empty) =
      TypeParameter(FreshIdentifier(name), flags)
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

  /* Dependent Types */

  private object TypeNormalization {
    private class TypeNormalizer extends SelfTreeTransformer {
      private val subst: MutableMap[Variable, Variable] = MutableMap.empty
      private var counter: Int = 0

      override def transform(expr: Expr): Expr = expr match {
        case v: Variable => subst.getOrElse(v, super.transform(v))
        case _ => super.transform(expr)
      }

      override def transform(vd: ValDef): ValDef = {
        val nid = new Identifier("x", counter, counter, false)
        counter += 1

        val newVd = ValDef(nid, transform(vd.tpe), vd.flags map transform).copiedFrom(vd)
        subst(vd.toVariable) = newVd.toVariable
        newVd
      }
    }

    def apply[T <: Type](tpe: T): T = (new TypeNormalizer).transform(tpe).asInstanceOf[T]
  }

  protected sealed trait TypeNormalization { self: Type with Product =>
    @inline
    private def elements: List[Any] = _elements.get
    private[this] val _elements: utils.Lazy[List[Any]] = utils.Lazy({
      // @nv: note that we can't compare `normalized` directly as we are
      //      overriding the `equals` method and this would lead to non-termination.
      val normalized = TypeNormalization(this)
      normalized.productIterator.toList
    })

    protected final def same(that: TypeNormalization): Boolean = elements == that.elements

    private[this] val _code: utils.Lazy[Int] = utils.Lazy(elements.hashCode)
    protected final def code: Int = _code.get
  }

  sealed case class PiType(params: Seq[ValDef], to: Type) extends Type with TypeNormalization {
    require(params.nonEmpty)

    override protected def computeType(implicit s: Symbols): Type =
      unveilUntyped(FunctionType(params.map(_.getType), to.getType))

    override def hashCode: Int = 31 * code
    override def equals(that: Any): Boolean = that match {
      case pi: PiType => this same pi
      case _ => false
    }
  }

  sealed case class SigmaType(params: Seq[ValDef], to: Type) extends Type with TypeNormalization {
    require(params.nonEmpty)

    override protected def computeType(implicit s: Symbols): Type =
      unveilUntyped(TupleType(params.map(_.getType) :+ to.getType))

    override def hashCode: Int = 53 * code
    override def equals(that: Any): Boolean = that match {
      case sigma: SigmaType => this same sigma
      case _ => false
    }
  }

  sealed case class RefinementType(vd: ValDef, prop: Expr) extends Type with TypeNormalization {
    override protected def computeType(implicit s: Symbols): Type =
      checkParamType(prop, BooleanType(), vd.getType)

    override def hashCode: Int = 79 * code
    override def equals(that: Any): Boolean = that match {
      case ref: RefinementType => this same ref
      case _ => false
    }
  }

  /* Utility methods for type checking */

  protected final def checkParamType(real: Typed, formal: Typed, result: => Type)(implicit s: Symbols) = {
    if (s.isSubtypeOf(real.getType, formal.getType)) result.getType else Untyped
  }

  protected final def checkParamTypes(real: Seq[Typed], formal: Seq[Typed], result: => Type)(implicit s: Symbols) = {
    if (
      real.size == formal.size &&
      (real zip formal forall (p => s.isSubtypeOf(p._1.getType, p._2.getType)))
    ) result.getType else Untyped
  }

  protected final def checkAllTypes(real: Seq[Typed], formal: Typed, result: => Type)(implicit s: Symbols) = {
    checkParamTypes(real, List.fill(real.size)(formal), result)
  }

  protected implicit class TypeWrapper(tpe: Type) {
    def orElse(other: => Type): Type = if (tpe == Untyped) other else tpe
  }

  /* Override points for supporting more complex types */

  protected final def getIntegerType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type =
    checkAllTypes(tpe +: tpes, IntegerType(), IntegerType())

  protected final def getRealType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type =
    checkAllTypes(tpe +: tpes, RealType(), RealType())

  protected def getBVType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type = tpe.getType match {
    case bv: BVType => checkAllTypes(tpes, bv, bv)
    case _ => Untyped
  }

  protected final def getCharType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type =
    checkAllTypes(tpe +: tpes, CharType(), CharType())

  protected def getADTType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type = tpe.getType match {
    case adt: ADTType => checkAllTypes(tpes, adt, adt)
    case _ => Untyped
  }

  protected def getTupleType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type = tpe.getType match {
    case tt: TupleType => checkAllTypes(tpes, tt, tt)
    case _ => Untyped
  }

  protected def getSetType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type = tpe.getType match {
    case st: SetType => checkAllTypes(tpes, st, st)
    case _ => Untyped
  }

  protected def getBagType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type = tpe.getType match {
    case bt: BagType => checkAllTypes(tpes, bt, bt)
    case _ => Untyped
  }

  protected def getMapType(tpe: Typed, tpes: Typed*)(implicit s: Symbols): Type = tpe.getType match {
    case mt: MapType => checkAllTypes(tpes, mt, mt)
    case _ => Untyped
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
      val (ids, vs, es, tps, flags, recons) = deconstructor.deconstruct(t)
      Some((tps, tps => recons(ids, vs, es, tps, flags)))
    }
  }

  object typeOps extends {
    protected val sourceTrees: self.type = self
    protected val targetTrees: self.type = self
  } with GenTreeOps {
    type Source = self.Type
    type Target = self.Type
    lazy val Deconstructor = NAryType

    def typeParamsOf(t: Type): Set[TypeParameter] = t match {
      case tp: TypeParameter => Set(tp)
      case NAryType(subs, _) =>
        subs.flatMap(typeParamsOf).toSet
    }

    def instantiateType(tpe: Type, tps: Map[TypeParameter, Type]): Type = {
      if (tps.isEmpty) {
        tpe
      } else {
        typeOps.postMap {
          case tp: TypeParameter => tps.get(tp)
          case _ => None
        } (tpe)
      }
    }

    // Helpers for instantiateType
    class TypeInstantiator(tps: Map[TypeParameter, Type]) extends SelfTreeTransformer {
      override def transform(tpe: Type): Type = tpe match {
        case tp: TypeParameter => tps.getOrElse(tp, super.transform(tpe))
        case _ => super.transform(tpe)
      }
    }

    def instantiateType(e: Expr, tps: Map[TypeParameter, Type]): Expr = {
      if (tps.isEmpty) {
        e
      } else {
        new TypeInstantiator(tps).transform(e)
      }
    }

    def isParametricType(tpe: Type): Boolean = tpe match {
      case (tp: TypeParameter) => true
      case NAryType(tps, builder) => tps.exists(isParametricType)
    }

    def replaceFromSymbols[V <: VariableSymbol](subst: Map[V, Expr], tpe: Type)
                                               (implicit ev: VariableConverter[V]): Type = {
      new SelfTreeTransformer {
        override def transform(expr: Expr): Expr = expr match {
          case v: Variable => subst.getOrElse(v.to[V], v)
          case _ => super.transform(expr)
        }
      }.transform(tpe)
    }

    def variablesOf(tpe: Type): Set[Variable] = tpe match {
      case PiType(params, to) =>
        params.foldRight(variablesOf(to)) {
          case (vd, vars) => vars - vd.toVariable ++ variablesOf(vd.tpe)
        }
      case SigmaType(params, to) =>
        params.foldRight(variablesOf(to)) {
          case (vd, vars) => vars - vd.toVariable ++ variablesOf(vd.tpe)
        }
      case RefinementType(vd, pred) =>
        exprOps.variablesOf(pred) - vd.toVariable ++ variablesOf(vd.tpe)
      case NAryType(tpes, _) => tpes.flatMap(variablesOf).toSet
    }

    class TypeSimplifier(implicit symbols: Symbols) extends SelfTreeTransformer {
      override def transform(tpe: Type): Type = tpe match {
        case (_: PiType | _: SigmaType | _: FunctionType) => tpe.getType
        case _ => super.transform(tpe)
      }
    }

    def simplify(expr: Expr)(implicit symbols: Symbols): Expr = new TypeSimplifier().transform(expr)
  }
}

