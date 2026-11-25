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

  protected def unveilUntyped(tpe: Type)(using s: Symbols): Type = {
    val NAryType(tps, _) = tpe: @unchecked
    if (tps contains Untyped) Untyped
    else tpe match {
      // sets, bags and maps compute with the equality of their elements and keys, and generic
      // code with the equality of its type parameters, which would observe a proposition
      case SetType(base) if s.containsProposition(base) => Untyped
      case BagType(base) if s.containsProposition(base) => Untyped
      case MapType(from, _) if s.containsProposition(from) => Untyped
      case ADTType(_, tps) if tps exists s.containsProposition => Untyped
      case _ => tpe
    }
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
    * A proposition has a truth value in every model but no evaluation rule, so its truth value
    * can't be observed: nothing takes a proposition back to a boolean. A term can't branch on
    * one, unless its branches are propositions themselves, and an equality between values that
    * hold propositions is a proposition (see [[TypeOps.containsProposition]]).
    *
    * A proposition is otherwise a value: it can be bound by a `Let` (a name for it), passed as
    * an argument, returned by a function (a predicate definition) or by a lambda (a predicate),
    * and held by a tuple, the field of an ADT or the values of a map. It can be refined by a
    * [[RefinementType]]. Since sets, bags and maps compute with the equality of their elements
    * and keys, and generic code with the equality of its type parameters, a proposition can't be
    * an element, a key or a type argument. One can't quantify over propositions.
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
    /** Renames the binders of a type to the identifiers of `SymbolOps.getId`, in order, as
      * `normalizeStructure` does for lambdas. The free variables of a type keep their names, and may
      * themselves be such identifiers (eg. in the body of a normalized lambda), so these are skipped.
      */
    private class TypeNormalizer(free: Set[Identifier]) extends ConcreteSelfTreeTransformer {
      private val subst: MutableMap[Variable, Variable] = MutableMap.empty
      private var counter: Int = 0

      private def nextId(): Identifier = {
        var id = SymbolOps.getId(counter)
        counter += 1
        while (free(id)) {
          id = SymbolOps.getId(counter)
          counter += 1
        }
        id
      }

      override def transform(expr: Expr): Expr = expr match {
        case v: Variable => subst.getOrElse(v, v)
        case _ => super.transform(expr)
      }

      override def transform(vd: ValDef): ValDef = {
        val nid = nextId()

        val newVd = ValDef(nid, transform(vd.tpe), vd.flags map transform).copiedFrom(vd)
        subst(vd.toVariable) = newVd.toVariable
        newVd
      }
    }

    def apply[T <: Type](tpe: T): T =
      (new TypeNormalizer(typeOps.variablesOf(tpe).map(_.id))).transform(tpe).asInstanceOf[T]
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

  /** Extracts the component types of any Type, as [[NAryType]] does, and also the types of the
    * variables that pi, sigma and refinement types bind: the parameter types of a pi or sigma type,
    * then its result type, and the base type of a refinement. Refinement predicates aren't types,
    * so they stay as they are.
    *
    * When the builder changes the type of a bound variable, it substitutes the variable at its new
    * type in the types and the predicate that can refer to it.
    */
  val BinderType: BinderTypeImpl = new BinderTypeImpl(self, self)

  class BinderTypeImpl(override protected val s: self.type,
                       override protected val t: self.type) extends TreeExtractor {
    type Source = Type
    type Target = Type

    // The parameters `params` at the types `tps`, where each type can refer to the parameters
    // before it, and the substitution of the parameters whose type changed
    private def rebind(params: Seq[ValDef], tps: Seq[Type]): (Seq[ValDef], Map[ValDef, Expr]) =
      (params zip tps).foldLeft((Seq.empty[ValDef], Map.empty[ValDef, Expr])) {
        case ((nparams, subst), (vd, tp)) =>
          val ntp = if (subst.isEmpty) tp else typeOps.replaceFromSymbols(subst, tp)
          if (ntp == vd.tpe) (nparams :+ vd, subst)
          else {
            val nvd = vd.copy(tpe = ntp).copiedFrom(vd)
            (nparams :+ nvd, subst + (vd -> nvd.toVariable))
          }
      }

    private def substitute(subst: Map[ValDef, Expr], tpe: Type): Type =
      if (subst.isEmpty) tpe else typeOps.replaceFromSymbols(subst, tpe)

    def unapply(t: Type): Option[(Seq[Type], Seq[Type] => Type)] = t match {
      case PiType(params, to) =>
        Some((params.map(_.tpe) :+ to, tps => {
          val (nparams, subst) = rebind(params, tps.init)
          PiType(nparams, substitute(subst, tps.last)).copiedFrom(t)
        }))
      case SigmaType(params, to) =>
        Some((params.map(_.tpe) :+ to, tps => {
          val (nparams, subst) = rebind(params, tps.init)
          SigmaType(nparams, substitute(subst, tps.last)).copiedFrom(t)
        }))
      case RefinementType(vd, pred) =>
        Some((Seq(vd.tpe), tps => {
          val (Seq(nvd), subst) = rebind(Seq(vd), tps): @unchecked
          RefinementType(nvd, if (subst.isEmpty) pred else exprOps.replaceFromSymbols(subst, pred)).copiedFrom(t)
        }))
      case NAryType(tps, recons) => Some((tps, recons))
    }
  }

  val typeOps: TypeOpsUtils = new TypeOpsUtils(self, self)

  final class TypeOpsUtils(override val sourceTrees: self.type, override val targetTrees: self.type) extends GenTreeOps {
    type Source = self.Type
    type Target = self.Type

    // The generic operations (`exists`, `collect`, `preMap`, ...) look into the types of the
    // variables that types bind, which an operation on the types of values must not miss
    val Deconstructor = BinderType

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

    /** Whether `tpe` mentions a type parameter, also in the types and predicates of bound variables. */
    def isParametricType(tpe: Type): Boolean = typeParamsOf(tpe).nonEmpty

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

