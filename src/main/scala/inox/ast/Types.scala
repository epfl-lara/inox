/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package ast

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait Types { self: Trees =>

  trait Typed extends Printable {
    def getTpe(stripRefinements: Boolean)(using Symbols): Type
    def getType(using Symbols): Type = getTpe(stripRefinements = true)
    def isTyped(using Symbols): Boolean = getType != Untyped
  }

  protected trait CachingTyped extends Typed {
    // The caches hold the `typingKey` of the symbol table that the type was computed with, not the
    // symbol table itself, which they would otherwise keep alive.
    private var cache: (AnyRef, Type) = (null, null)
    private var noRefinementsCache: (AnyRef, Type) = (null, null)

    final def getTpe(stripRefinements: Boolean)(using s: Symbols): Type = {
      val (key, tpe) = if (stripRefinements) noRefinementsCache else cache
      if ((key ne null) && (key eq s.typingKey)) tpe else {
        val tpe = computeTpe(stripRefinements)
        val entry = s.typingKey -> tpe
        if (stripRefinements) { noRefinementsCache = entry } else { cache = entry }
        tpe
      }
    }

    protected def computeTpe(stripRefinements: Boolean)(using Symbols): Type
  }

  protected def unveilUntyped(tpe: Type): Type = {
    val NAryType(tps, _) = tpe: @unchecked
    // propositions are not data: `PropType` can't appear inside of another type
    if (tps exists (tp => tp == Untyped || tp == PropType())) Untyped else tpe
  }

  abstract class Type extends Tree with Typed {
    private var simple: Boolean = false
    // See the caches of `CachingTyped`
    private var cache: (AnyRef, Type) = (null, null)

    private def setSimple(): this.type = { simple = true; this }

    final def getTpe(stripRefinements: Boolean)(using s: Symbols): Type =
      if (!stripRefinements || simple) this else {
        val (key, tpe) = cache
        if ((key ne null) && (key eq s.typingKey)) tpe else {
          val tpe = computeErasedType
          cache = s.typingKey -> tpe.setSimple()
          tpe
        }
      }

    protected def computeErasedType(using Symbols): Type = {
      val NAryType(tps, recons) = this: @unchecked
      unveilUntyped(recons(tps.map(_.getType)))
    }

    def stripToplevelRefinement: Type = this
  }

  case object Untyped extends Type

  case class BooleanType() extends Type

  /** The type of propositions, of which [[BooleanType]] is a subtype.
    *
    * A proposition has a truth value in every model but no evaluation rule, so the value of a
    * term can't depend on it: nothing takes a proposition back to a boolean. Propositions are not
    * data either. `PropType` is the type of an expression, of a variable that a `Let` binds to a
    * proposition (a name for it), or the return type of a function (a predicate definition). It
    * can't be the type of a parameter or a field, or appear inside of another type, other than
    * as the type that a [[RefinementType]] refines: a refined proposition is still a proposition.
    *
    * Propositions are accepted where a specification is stated: in the predicate of a
    * [[RefinementType]] or of an `Assume`, and in the constraints of solvers. Quantifiers are
    * propositions under [[QuantifierMode.Propositional]].
    */
  case class PropType()    extends Type
  case class UnitType()    extends Type
  case class CharType()    extends Type
  case class IntegerType() extends Type
  case class RealType()    extends Type
  case class StringType()  extends Type

  sealed case class BVType(signed: Boolean, size: Int) extends Type

  abstract class BVTypeExtractor(signed: Boolean, size: Int) {
    def apply(): BVType = BVType(signed, size)
    def unapply(tpe: BVType): Boolean = tpe.signed == signed && tpe.size == size
  }

  object Int8Type  extends BVTypeExtractor(true, 8)
  object Int16Type extends BVTypeExtractor(true, 16)
  object Int32Type extends BVTypeExtractor(true, 32)
  object Int64Type extends BVTypeExtractor(true, 64)

  sealed case class FPType(exponent: Int, significand: Int) extends Type

  abstract class FPTypeExtractor(exponent: Int, significand: Int) {
    def apply(): FPType = FPType(exponent, significand)

    def unapply(tpe: FPType): Boolean = tpe.exponent == exponent && tpe.significand == significand
  }
  
  object Float32Type extends FPTypeExtractor(8, 24)
  object Float64Type extends FPTypeExtractor(11, 53)

  object RoundingMode extends Type

  sealed case class TypeParameter(id: Identifier, flags: Seq[Flag]) extends Type {
    def freshen = TypeParameter(id.freshen, flags).copiedFrom(this)

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
    def lookupSort(using s: Symbols): Option[TypedADTSort] = s.lookupSort(id, tps)
    def getSort(using s: Symbols): TypedADTSort = s.getSort(id, tps)

    def getField(selector: Identifier)(using Symbols): Option[ValDef] = lookupSort match {
      case Some(tsort: TypedADTSort) =>
        tsort.constructors.flatMap(_.fields).collectFirst {
          case vd @ ValDef(`selector`, _, _) => vd
        }
      case _ => None
    }
  }

  /* Dependent Types */

  private object TypeNormalization {
    private class TypeNormalizer extends ConcreteSelfTreeTransformer {
      private val subst: MutableMap[Variable, Variable] = MutableMap.empty
      private var counter: Int = 0

      override def transform(expr: Expr): Expr = expr match {
        case v: Variable => subst.getOrElse(v, v)
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

  protected sealed trait TypeNormalization { self: Type & Product =>
    @inline
    private final def elements: List[Any] = _elements.get
    private val _elements: utils.Lazy[List[Any]] = utils.Lazy({
      // @nv: note that we can't compare `normalized` directly as we are
      //      overriding the `equals` method and this would lead to non-termination.
      val normalized: Type & Product = TypeNormalization[Type & Product](this)
      normalized.productIterator.toList
    })

    protected final def same(that: TypeNormalization): Boolean = elements == that.elements

    private val _code: utils.Lazy[Int] = utils.Lazy(elements.hashCode)
    protected final def code: Int = _code.get
  }

  sealed case class PiType(params: Seq[ValDef], to: Type) extends Type with TypeNormalization {
    require(params.nonEmpty)

    override protected def computeErasedType(using Symbols): Type =
      unveilUntyped(FunctionType(params.map(_.getType), to.getType))

    override def hashCode: Int = 31 * code
    override def equals(that: Any): Boolean = that match {
      case pi: PiType => this `same` pi
      case _ => false
    }
  }

  sealed case class SigmaType(params: Seq[ValDef], to: Type) extends Type with TypeNormalization {
    require(params.nonEmpty)

    override protected def computeErasedType(using Symbols): Type =
      unveilUntyped(TupleType(params.map(_.getType) :+ to.getType))

    override def hashCode: Int = 53 * code
    override def equals(that: Any): Boolean = that match {
      case sigma: SigmaType => this `same` sigma
      case _ => false
    }
  }

  sealed case class RefinementType(vd: ValDef, prop: Expr) extends Type with TypeNormalization {
    override protected def computeErasedType(using Symbols): Type =
      checkProposition(prop, vd.getType)

    override def hashCode: Int = 79 * code
    override def equals(that: Any): Boolean = that match {
      case ref: RefinementType => this `same` ref
      case _ => false
    }

    override def stripToplevelRefinement: Type = vd.tpe.stripToplevelRefinement
  }

  /* Utility methods for type checking */

  protected final def checkParamType(real: Typed, formal: Typed, result: => Type)(using s: Symbols) = {
    if (s.isSubtypeOf(real.getType, formal.getType)) result.getType else Untyped
  }

  protected final def checkParamTypes(real: Seq[Typed], formal: Seq[Typed], result: => Type)(using s: Symbols) = {
    if (
      real.size == formal.size &&
      (real zip formal forall (p => s.isSubtypeOf(p._1.getType, p._2.getType)))
    ) result.getType else Untyped
  }

  protected final def checkAllTypes(real: Seq[Typed], formal: Typed, result: => Type)(using Symbols) = {
    checkParamTypes(real, List.fill(real.size)(formal), result)
  }

  extension (tpe: Type) {
    protected def orElse(other: => Type): Type = if (tpe == Untyped) other else tpe
  }

  /** Whether `tpe` is the type of a proposition: a boolean, or `PropType`.
    *
    * This doesn't rely on booleans being a subtype of propositions, so that it holds under the
    * subtyping relations of trees that don't know of propositions. */
  protected final def isPropositional(tpe: Typed)(using s: Symbols): Boolean =
    s.isSubtypeOf(tpe.getType, BooleanType()) || tpe.getType == PropType()

  /** The type `result` if `real` is a proposition (see [[isPropositional]]). */
  protected final def checkProposition(real: Typed, result: => Type)(using Symbols): Type =
    if (isPropositional(real)) result.getType else Untyped

  /** The type of a connective over `operands`: a boolean if they all are, and a proposition if
    * some of them are propositions. */
  protected final def getPropositionalType(operands: Typed*)(using s: Symbols): Type = {
    val tpes = operands.map(_.getType)
    if (tpes.forall(s.isSubtypeOf(_, BooleanType()))) BooleanType()
    else if (tpes.forall(isPropositional(_))) PropType()
    else Untyped
  }

  /* Override points for supporting more complex types */

  protected final def getIntegerType(tpe: Typed, tpes: Typed*)(using Symbols): Type =
    checkAllTypes(tpe +: tpes, IntegerType(), IntegerType())

  protected final def getRealType(tpe: Typed, tpes: Typed*)(using Symbols): Type =
    checkAllTypes(tpe +: tpes, RealType(), RealType())

  protected def getBVType(tpe: Typed, tpes: Typed*)(using Symbols): Type = tpe.getType match {
    case bv: BVType => checkAllTypes(tpes, bv, bv)
    case _ => Untyped
  }

  protected def getFPType(tpe: Typed, tpes: Typed*)(using Symbols): Type = tpe.getType match {
    case f: FPType => checkAllTypes(tpes, f, f)
    case _ => Untyped
  }

  protected def getRoundingMode(tpe: Typed, tpes: Typed*)(using Symbols): Type =
    checkAllTypes(tpe +: tpes, RoundingMode, RoundingMode)

  protected final def getCharType(tpe: Typed, tpes: Typed*)(using Symbols): Type =
    checkAllTypes(tpe +: tpes, CharType(), CharType())

  protected def getADTType(tpe: Typed, tpes: Typed*)(using Symbols): Type = tpe.getType match {
    case adt: ADTType => checkAllTypes(tpes, adt, adt)
    case _ => Untyped
  }

  protected def getTupleType(tpe: Typed, tpes: Typed*)(using Symbols): Type = tpe.getType match {
    case tt: TupleType => checkAllTypes(tpes, tt, tt)
    case _ => Untyped
  }

  protected def getSetType(tpe: Typed, tpes: Typed*)(stripRefinements: Boolean)(using Symbols): Type = tpe.getType match {
    case st: SetType => checkAllTypes(tpes, st, if stripRefinements then st else tpe.getTpe(stripRefinements = false).stripToplevelRefinement)
    case _ => Untyped
  }

  protected def getBagType(tpe: Typed, tpes: Typed*)(stripRefinements: Boolean)(using Symbols): Type = tpe.getType match {
    case bt: BagType => checkAllTypes(tpes, bt, if stripRefinements then bt else tpe.getTpe(stripRefinements = false).stripToplevelRefinement)
    case _ => Untyped
  }

  protected def getMapType(tpe: Typed, tpes: Typed*)(stripRefinements: Boolean)(using Symbols): Type = tpe.getType match {
    case mt: MapType => checkAllTypes(tpes, mt, if stripRefinements then mt else tpe.getTpe(stripRefinements = false).stripToplevelRefinement)
    case _ => Untyped
  }

  /** NAryType extractor to extract any Type in a consistent way.
    *
    * @see [[Deconstructors.Operator]] about why we can't have nice(r) things
    */
  val NAryType: NAryTypeImpl = new NAryTypeImpl(self, self)

  class NAryTypeImpl(override protected val s: self.type,
                     override protected val t: self.type) extends TreeExtractor {
    type Source = Type
    type Target = Type

    def unapply(t: Type): Option[(Seq[Type], Seq[Type] => Type)] = {
      val (ids, vs, es, tps, flags, recons) = deconstructor.deconstruct(t)
      Some((tps, tps => recons(ids, vs, es, tps, flags)))
    }
  }

  val typeOps: TypeOpsUtils = new TypeOpsUtils(self, self)

  final class TypeOpsUtils(override val sourceTrees: self.type, override val targetTrees: self.type) extends GenTreeOps {
    type Source = self.Type
    type Target = self.Type

    val Deconstructor = NAryType

    // Helper for typeParamsOf
    class TypeCollector extends ConcreteSelfTreeTraverser {
      private val typeParams: MutableSet[TypeParameter] = MutableSet.empty
      def getResult: Set[TypeParameter] = typeParams.toSet

      override def traverse(tpe: Type): Unit = tpe match {
        case tp: TypeParameter => typeParams += tp
        case _ => super.traverse(tpe)
      }
    }

    def typeParamsOf(e: Expr): Set[TypeParameter] = {
      val collector = new TypeCollector
      collector.traverse(e)
      collector.getResult
    }

    def typeParamsOf(t: Type): Set[TypeParameter] = {
      val collector = new TypeCollector
      collector.traverse(t)
      collector.getResult
    }

    // Helpers for instantiateType
    class TypeInstantiator(tps: Map[TypeParameter, Type]) extends ConcreteSelfTreeTransformer {
      override def transform(tpe: Type): Type = tpe match {
        case tp: TypeParameter => tps.getOrElse(tp, super.transform(tpe))
        case _ => super.transform(tpe)
      }
    }

    def instantiateType(tpe: Type, tps: Map[TypeParameter, Type]): Type = {
      if (tps.isEmpty) {
        tpe
      } else {
        new TypeInstantiator(tps).transform(tpe)
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
                                               (using VariableConverter[V]): Type = {
      new ConcreteSelfTreeTransformer {
        override def transform(expr: Expr): Expr = expr match {
          case v: Variable if subst.contains(v.to[V]) => subst(v.to[V])
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

    class TypeSimplifier(using symbols: Symbols) extends ConcreteSelfTreeTransformer {
      override def transform(tpe: Type): Type = tpe match {
        case (_: PiType | _: SigmaType | _: FunctionType) => tpe.getType
        case _ => super.transform(tpe)
      }
    }

    def simplify(expr: Expr)(using Symbols): Expr = new TypeSimplifier().transform(expr)
  }
}

