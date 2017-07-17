/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

/** Performs incremental ADT unfolding and enables support for ADT invariants as well
  * as support for first-class functions within ADTs.
  *
  * ADT unfolding is also used to discover fist-class functions over which a given
  * lambda will close (closures of the resulting "closure"). These are necessary to
  * support equality between input first-class functions and lambdas defined within
  * the current expression as there must exist a total order on the closure
  * definitions to avoid impossible closure creation deadlocks.
  *
  * @see [[LambdaTemplates]] for more discussions about input first-class functions
  *                          and the total ordering of closures.
  */
trait DatatypeTemplates { self: Templates =>
  import program._
  import program.trees._
  import program.symbols._

  import datatypesManager._

  type Functions = Set[(Encoded, FunctionType, Encoded)]

  /** Represents the kind of datatype a given template is associated to. */
  sealed abstract class TypeInfo {
    def getType: Type = this match {
      case SortInfo(tsort) => tsort.toType
      case SetInfo(base) => SetType(base)
      case BagInfo(base) => BagType(base)
      case MapInfo(from, to) => MapType(from, to)
    }
  }

  case class SortInfo(tsort: TypedADTSort) extends TypeInfo
  case class SetInfo(base: Type) extends TypeInfo
  case class BagInfo(base: Type) extends TypeInfo
  case class MapInfo(from: Type, to: Type) extends TypeInfo
 
  /** Represents the kind of instantiator (@see [[TypesTemplate]]) a given
    * template info is associated to. */
  sealed abstract class TemplateInstantiator {
    def substitute(substituter: Encoded => Encoded): TemplateInstantiator = this match {
      case Datatype => Datatype
      case Capture(encoded, tpe) => Capture(substituter(encoded), tpe)
      case Invariant => Invariant
    }
  }

  case object Datatype extends TemplateInstantiator
  case class Capture(encoded: Encoded, tpe: FunctionType) extends TemplateInstantiator
  case object Invariant extends TemplateInstantiator

  /** Represents a type unfolding of a free variable (or input) in the unfolding procedure */
  case class TemplateTypeInfo(info: TypeInfo, arg: Encoded, instantiator: TemplateInstantiator) {
    override def toString: String =
      info + "(" + asString(arg) + ")" + (instantiator match {
        case Capture(f, tpe) => " in " + asString(f)
        case _ => ""
      })

    def substitute(substituter: Encoded => Encoded): TemplateTypeInfo = copy(
      arg = substituter(arg),
      instantiator = instantiator.substitute(substituter)
    )
  }

  /** Sets up the relevant unfolding procedures for symbols that are free in the input expression */
  def registerSymbol(start: Encoded, sym: Encoded, tpe: Type): Clauses = {
    DatatypeTemplate(tpe).instantiate(start, sym)
  }

  /** Sets up the relevant unfolding procedure for closure ordering */
  def registerClosure(start: Encoded, container: (Encoded, FunctionType), arg: (Encoded, Type)): Clauses = {
    CaptureTemplate(arg._2, container._2).instantiate(start, container._1, arg._1)
  }

  /** Sets up the relevant unfolding procedure for datatype invariant instantiation. */
  def unrollInvariant(start: Encoded, sym: Encoded, tpe: Type): Clauses = {
    InvariantTemplate(tpe).instantiate(start, sym)
  }

  /** Base trait for datatype unfolding template generators.
    *
    * This trait provides a useful interface for building datatype unfolding
    * templates. The interesting override points are:
    *
    * - [[unroll]]:
    *   determines whether a given type requires unfolding.
    *   @see [[ADTUnrolling.unroll]]
    *   @see [[FunctionUnrolling.unroll]]
    *   @see [[FlatUnrolling.unroll]]
    *   @see [[CachedUnrolling.unroll]]
    *
    * - [[Builder.rec]]:
    *   can be overriden to provide finer controll of what clauses should be generated during
    *   template construction. The [[Builder]] class itself can't be overriden, so one must be
    *   careful to use the overriding class when construction a template! We use a [[Builder]]
    *   class here so that the [[Builder.rec]] method can refer to the current [[Builder]]
    *   state while still providing an override point.
    *   @see [[DatatypeTemplate.Builder.rec]]
    *   @see [[CaptureTemplate.Builder.rec]]
    *
    * @see [[DatatypeTemplate$]]
    * @see [[CaptureTemplate$]]
    */
  sealed protected trait TemplateGenerator {
    /** Determines whether a given [[ast.Types.Type Type]] needs to be considered during ADT unfolding. */
    def unroll(tpe: Type): Boolean

    /** Stateful template generating trait. Provides the [[rec]] override point so that
      * subclasses of [[TemplateGenerator]] can override [[rec]] while still using
      * stateful clause generation.
      */
    protected trait Builder {
      val tpe: Type

      val v = Variable.fresh("x", tpe, true)
      val pathVar = Variable.fresh("b", BooleanType, true)
      val (idT, pathVarT) = (encodeSymbol(v), encodeSymbol(pathVar))

      private var exprVars = Map[Variable, Encoded]()
      @inline protected def storeExpr(v: Variable): Unit = {
        exprVars += v -> encodeSymbol(v)
      }

      private var condVars = Map[Variable, Encoded]()
      private var condTree = Map[Variable, Set[Variable]](pathVar -> Set.empty).withDefaultValue(Set.empty)
      @inline protected def storeCond(pathVar: Variable, v: Variable): Unit = {
        condVars += v -> encodeSymbol(v)
        condTree += pathVar -> (condTree(pathVar) + v)
      }

      private var guardedExprs = Map[Variable, Seq[Expr]]()
      @inline protected def storeGuarded(pathVar: Variable, expr: Expr): Unit = {
        val prev = guardedExprs.getOrElse(pathVar, Nil)
        guardedExprs += pathVar -> (expr +: prev)
      }

      private var equations = Seq[Expr]()
      @inline protected def iff(e1: Expr, e2: Expr): Unit = equations :+= Equals(e1, e2)

      private var tpes = Map[Variable, Set[(TypeInfo, Expr)]]()
      @inline protected def storeType(pathVar: Variable, info: TypeInfo, arg: Expr): Unit = {
        tpes += pathVar -> (tpes.getOrElse(pathVar, Set.empty) + (info -> arg))
      }

      protected def isRelevantBlocker(v: Variable): Boolean = {
        (tpes contains v) ||
        (guardedExprs contains v) ||
        guardedExprs.exists(_._2.exists(e => exprOps.variablesOf(e)(v)))
      }

      protected case class RecursionState(
        recurseSort: Boolean, // visit sort children
        recurseMap: Boolean,  // unroll map definition
        recurseSet: Boolean,  // unroll set definition
        recurseBag: Boolean   // unroll bag definition
      )

      /** Generates the clauses and other bookkeeping relevant to a type unfolding template.
        * Subtypes of [[Builder]] can override this method to change clause generation. */
      protected def rec(pathVar: Variable, expr: Expr, state: RecursionState): Unit = expr.getType match {
        case tpe if !unroll(tpe) =>
          // nothing to do here!

        case adt: ADTType =>
          val tadt = adt.getADT

          if (tadt.definition.isSort && tadt.toSort.definition.isInductive && !state.recurseSort) {
            storeType(pathVar, SortInfo(tadt.toSort), expr)
          } else {
            val matchers = tadt.root match {
              case (tsort: TypedADTSort) => tsort.constructors
              case (tcons: TypedADTConstructor) => Seq(tcons)
            }

            for (tcons <- matchers) {
              val tpe = tcons.toType

              if (unroll(tpe)) {
                val newBool: Variable = Variable.fresh("b", BooleanType, true)
                storeCond(pathVar, newBool)

                for (vd <- tcons.fields) {
                  val ex = if (adt != tpe) AsInstanceOf(expr, tpe) else expr
                  rec(newBool, ADTSelector(ex, vd.id), state.copy(recurseSort = false))
                }

                if (isRelevantBlocker(newBool)) {
                  iff(and(pathVar, IsInstanceOf(expr, tpe)), newBool)
                }
              }
            }
          }

        case TupleType(tpes) =>
          for ((_, idx) <- tpes.zipWithIndex) {
            rec(pathVar, TupleSelect(expr, idx + 1), state)
          }

        case MapType(from, to) =>
          val newBool: Variable = Variable.fresh("b", BooleanType, true)
          storeCond(pathVar, newBool)

          val dfltExpr: Variable = Variable.fresh("dlft", to, true)
          storeExpr(dfltExpr)

          iff(and(pathVar, Not(Equals(expr, FiniteMap(Seq.empty, dfltExpr, from, to)))), newBool)
          rec(pathVar, dfltExpr, state)

          if (!state.recurseMap) {
            storeType(newBool, MapInfo(from, to), expr)
          } else {
            val keyExpr: Variable = Variable.fresh("key", from, true)
            val valExpr: Variable = Variable.fresh("val", to, true)
            val restExpr: Variable = Variable.fresh("rest", MapType(from, to), true)
            storeExpr(keyExpr)
            storeExpr(valExpr)
            storeExpr(restExpr)

            storeGuarded(newBool, Equals(expr, MapUpdated(restExpr, keyExpr, valExpr)))
            rec(newBool, restExpr, state.copy(recurseMap = false))
            rec(newBool, keyExpr, state)
            rec(newBool, valExpr, state)
          }

        case SetType(base) =>
          val newBool: Variable = Variable.fresh("b", BooleanType, true)
          storeCond(pathVar, newBool)

          iff(and(pathVar, Not(Equals(expr, FiniteSet(Seq.empty, base)))), newBool)

          if (!state.recurseSet) {
            storeType(newBool, SetInfo(base), expr)
          } else {
            val elemExpr: Variable = Variable.fresh("elem", base, true)
            val restExpr: Variable = Variable.fresh("rest", SetType(base), true)
            storeExpr(elemExpr)
            storeExpr(restExpr)

            storeGuarded(newBool, Equals(expr, SetUnion(FiniteSet(Seq(elemExpr), base), restExpr)))
            rec(newBool, restExpr, state.copy(recurseSet = false))
            rec(newBool, elemExpr, state)
          }

        case BagType(base) =>
          val newBool: Variable = Variable.fresh("b", BooleanType, true)
          storeCond(pathVar, newBool)

          iff(and(pathVar, Not(Equals(expr, FiniteBag(Seq.empty, base)))), newBool)

          if (!state.recurseBag) {
            storeType(pathVar, BagInfo(base), expr)
          } else {
            val elemExpr: Variable = Variable.fresh("elem", base, true)
            val multExpr: Variable = Variable.fresh("mult", IntegerType, true)
            val restExpr: Variable = Variable.fresh("rest", BagType(base), true)
            storeExpr(elemExpr)
            storeExpr(multExpr)
            storeExpr(restExpr)

            storeGuarded(newBool, Equals(expr, BagUnion(FiniteBag(Seq(elemExpr -> multExpr), base), restExpr)))
            storeGuarded(newBool, GreaterThan(multExpr, IntegerLiteral(0)))
            rec(newBool, restExpr, state.copy(recurseBag = false))
            rec(newBool, elemExpr, state)
          }

        case _ => throw FatalError("Unexpected unrollable")
      }

      /* Calls [[rec]] and finalizes the bookkeeping collection before returning everything
       * necessary to a template creation. */
      lazy val (encoder, conds, exprs, tree, clauses, calls, types) = {
        rec(pathVar, v, RecursionState(true, true, true, true))

        val encoder: Expr => Encoded = mkEncoder(exprVars ++ condVars + (v -> idT) + (pathVar -> pathVarT))

        var clauses: Clauses = Seq.empty
        var calls: CallBlockers  = Map.empty

        for ((b, es) <- guardedExprs) {
          var callInfos : Set[Call] = Set.empty

          for (e <- es) {
            callInfos ++= firstOrderCallsOf(e).map { case (id, tps, args) =>
              Call(getFunction(id, tps), args.map(arg => Left(encoder(arg))))
            }

            clauses :+= encoder(Implies(b, e))
          }

          if (callInfos.nonEmpty) calls += encoder(b) -> callInfos
        }

        clauses ++= equations.map(encoder)

        val encodedTypes: Map[Encoded, Set[(TypeInfo, Encoded)]] = tpes.map { case (b, tps) =>
          encoder(b) -> tps.map { case (info, expr) => (info, encoder(expr)) }
        }

        (encoder, condVars, exprVars, condTree, clauses, calls, encodedTypes)
      }
    }
  }

  /** Extends [[TemplateGenerator]] with functionalities for checking whether
    * ADTs need to be unrolled.
    *
    * Note that the actual ADT unrolling takes place in [[TemplateGenerator.Builder.rec]].
    */
  protected trait ADTUnrolling extends TemplateGenerator {
    private val checking: MutableSet[TypedADTDefinition] = MutableSet.empty

    /** We recursively visit the ADT and its fields here to check whether we need to unroll. */
    abstract override def unroll(tpe: Type): Boolean = tpe match {
      case adt: ADTType => adt.getADT match {
        case tadt if checking(tadt.root) => false
        case tadt =>
          checking += tadt.root
          val constructors = tadt.root match {
            case tsort: TypedADTSort => tsort.constructors
            case tcons: TypedADTConstructor => Seq(tcons)
          }

          constructors.exists(c => c.fieldsTypes.exists(unroll))
      }

      case _ => super.unroll(tpe)
    }
  }

  /** Extends [[TemplateGenerator]] with functionalities to accumulate the set
    * of functions contained within a datastructure.
    */
  protected trait FunctionUnrolling extends TemplateGenerator {

    /** The definition of [[unroll]] makes sure ALL functions are discovered. */
    def unroll(tpe: Type): Boolean = tpe match {
      case BooleanType | UnitType | CharType | IntegerType |
           RealType | StringType | (_: BVType) | (_: TypeParameter) => false

      case (_: FunctionType) | (_: BagType) | (_: SetType) => true

      case NAryType(tpes, _) => tpes.exists(unroll)
    }

    /** The [[TemplateGenerator.Builder]] trait is extended to accumulate functions
      * during the clause generation. */
    protected trait Builder extends super.Builder {
      private var functions = Map[Variable, Set[Expr]]()
      @inline protected def storeFunction(pathVar: Variable, expr: Expr): Unit = {
        functions += pathVar -> (functions.getOrElse(pathVar, Set.empty) + expr)
      }

      override protected def isRelevantBlocker(v: Variable): Boolean = {
        super.isRelevantBlocker(v) || (functions contains v)
      }

      override protected def rec(pathVar: Variable, expr: Expr, state: RecursionState): Unit = expr.getType match {
        case _: FunctionType => storeFunction(pathVar, expr)
        case _ => super.rec(pathVar, expr, state)
      }

      lazy val funs: Functions = {
        val enc = encoder // forces super to call rec()
        functions.flatMap { case (b, fs) =>
          val bp = enc(b)
          fs.map(expr => (bp, bestRealType(expr.getType).asInstanceOf[FunctionType], enc(expr)))
        }.toSet
      }
    }
  }

  /** Template generator that ensures [[unroll]] call results are cached. */
  protected trait CachedUnrolling extends TemplateGenerator {
    private val unrollCache: MutableMap[Type, Boolean] = MutableMap.empty

    /** Determines whether a given [[ast.Types.Type Type]] needs to be considered during ADT unfolding.
      * 
      * This function DOES NOT correspond to an override point (hence the `final` modifier).
      * One should look at [[unrollType]] to change the behavior of [[unroll]].
      */
    abstract override final def unroll(tpe: Type): Boolean = unrollCache.getOrElseUpdate(tpe, {
      unrollType(tpe) || super.unroll(tpe)
    })

    /** Override point to determine whether a given type should be unfolded.
      *
      * This methods shouldn't be recursive as the ADT traversal already takes place
      * within the [[unroll]] method.
      *
      * By default, returns `false`.
      */
    protected def unrollType(tpe: Type): Boolean = false
  }

  /** Template generator that generates clauses for ADT invariant assertion. */
  protected trait InvariantGenerator
    extends TemplateGenerator
       with ADTUnrolling
       with CachedUnrolling {

    /** ADT unfolding is required when either:
     * 1. a constructor type is required and it has a super-type (SMT solvers
     *    are blind to this case), or
     * 2. the ADT type has an ADT invariant.
     *
     * Note that clause generation in [[Builder.rec]] MUST correspond to the types
     * that require unfolding as defined here.
     */
    override protected def unrollType(tpe: Type): Boolean = tpe match {
      case adt: ADTType => adt.getADT match {
        case tcons: TypedADTConstructor if tcons.sort.isDefined => true
        case tdef => tdef.hasInvariant
      }
      case _ => false
    }

    /** Clause generation is specialized to handle ADT constructor types that require
      * type guards as well as ADT invariants. */
    protected trait Builder extends super.Builder {
      override protected def rec(pathVar: Variable, expr: Expr, state: RecursionState): Unit = expr.getType match {
        case adt: ADTType =>
          val tadt = adt.getADT

          if (tadt.hasInvariant) {
            storeGuarded(pathVar, tadt.invariant.get.applied(Seq(expr)))
          }

          if (tadt != tadt.root) {
            storeGuarded(pathVar, IsInstanceOf(expr, tadt.toType))

            val tpe = tadt.toType
            for (vd <- tadt.toConstructor.fields) {
              rec(pathVar, ADTSelector(AsInstanceOf(expr, tpe), vd.id), state.copy(recurseSort = false))
            }
          } else {
            super.rec(pathVar, expr, state)
          }

        case _ => super.rec(pathVar, expr, state)
      }
    }
  }

  /** Base type for datatype unfolding templates. */
  trait TypesTemplate extends Template {
    val contents: TemplateContents
    val types: Map[Encoded, Set[TemplateTypeInfo]]

    override def instantiate(substMap: Map[Encoded, Arg]): Clauses = {
      val substituter = mkSubstituter(substMap.mapValues(_.encoded))

      for ((b, tps) <- types; bp = substituter(b); tp <- tps) {
        val stp = tp.copy(arg = substituter(tp.arg))
        val gen = nextGeneration(currentGeneration)
        val notBp = mkNot(bp)

        typeInfos.get(bp) match {
          case Some((exGen, origGen, _, exTps)) =>
            val minGen = gen min exGen
            typeInfos += bp -> (minGen, origGen, notBp, exTps + stp)
          case None =>
            typeInfos += bp -> (gen, gen, notBp, Set(stp))
        }
      }

      super.instantiate(substMap)
    }
  }

  /** Template used to unfold free symbols in the input expression. */
  class DatatypeTemplate private[DatatypeTemplates] (
    val contents: TemplateContents,
    val types: Map[Encoded, Set[TemplateTypeInfo]],
    val functions: Functions) extends TypesTemplate {

    def instantiate(blocker: Encoded, arg: Encoded): Clauses = {
      instantiate(blocker, Seq(Left(arg)))
    }

    override def instantiate(substMap: Map[Encoded, Arg]): Clauses = {
      val substituter = mkSubstituter(substMap.mapValues(_.encoded))

      val clauses: Clauses = (for ((b,tpe,f) <- functions) yield {
        registerFunction(substituter(b), tpe, substituter(f))
      }).flatten.toSeq

      clauses ++ super.instantiate(substMap)
    }
  }

  /** Generator for [[DatatypeTemplate]] instances. */
  object DatatypeTemplate extends FunctionUnrolling with InvariantGenerator {
    private val cache: MutableMap[Type, DatatypeTemplate] = MutableMap.empty

    def apply(dtpe: Type): DatatypeTemplate = cache.getOrElseUpdate(dtpe, {
      object b extends {
        val tpe = dtpe
      } with super[FunctionUnrolling].Builder
        with super[InvariantGenerator].Builder

      val typeBlockers: TypeBlockers = b.types.map { case (blocker, tps) =>
        blocker -> tps.map { case (info, arg) => TemplateTypeInfo(info, arg, Datatype) }
      }

      new DatatypeTemplate(TemplateContents(
        b.pathVar -> b.pathVarT, Seq(b.v -> b.idT),
        b.conds, b.exprs, Map.empty, b.tree, b.clauses, b.calls,
        Map.empty, Map.empty, Map.empty, Seq.empty, Seq.empty, Map.empty), typeBlockers, b.funs)
    })
  }

  /** Template used to unfold ADT closures that may contain functions. */
  class CaptureTemplate private[DatatypeTemplates](
    val contents: TemplateContents,
    val types: Map[Encoded, Set[TemplateTypeInfo]],
    val functions: Set[Encoded]) extends TypesTemplate {

    val Seq((_, container), _) = contents.arguments

    def instantiate(blocker: Encoded, container: Encoded, arg: Encoded): Clauses = {
      instantiate(blocker, Seq(Left(container), Left(arg)))
    }

    override def instantiate(substMap: Map[Encoded, Arg]): Clauses = {
      val substituter = mkSubstituter(substMap.mapValues(_.encoded))

      val sc = substituter(container)
      val sfuns = functions.map(substituter)

      lessOrder += sc -> (lessOrder(sc) ++ sfuns)

      super.instantiate(substMap)
    }
  }

  /** Template generator for [[CaptureTemplate]] instances. */
  object CaptureTemplate
    extends FunctionUnrolling
       with ADTUnrolling
       with CachedUnrolling {

    private val tmplCache: MutableMap[Type, (
      (Variable, Encoded),
      (Variable, Encoded),
      Map[Variable, Encoded],
      Map[Variable, Encoded],
      Map[Variable, Set[Variable]],
      Clauses,
      Map[Encoded, Set[(TypeInfo, Encoded)]],
      Functions
    )] = MutableMap.empty

    private val cache: MutableMap[(Type, FunctionType), CaptureTemplate] = MutableMap.empty
    private val ordCache: MutableMap[FunctionType, Encoded => Encoded] = MutableMap.empty

    private val lessThan: (Encoded, Encoded) => Encoded = {
      val l = Variable.fresh("left", IntegerType)
      val r = Variable.fresh("right", IntegerType)
      val (lT, rT) = (encodeSymbol(l), encodeSymbol(r))

      val encoded = mkEncoder(Map(l -> lT, r -> rT))(LessThan(l, r))
      (nl: Encoded, nr: Encoded) => mkSubstituter(Map(lT -> nl, rT -> nr))(encoded)
    }

    private def order(tpe: FunctionType): Encoded => Encoded = ordCache.getOrElseUpdate(tpe, {
      val a = Variable.fresh("arg", tpe)
      val o = Variable.fresh("order", FunctionType(Seq(tpe), IntegerType), true)
      val (aT, oT) = (encodeSymbol(a), encodeSymbol(o))
      val encoded = mkEncoder(Map(a -> aT, o -> oT))(Application(o, Seq(a)))
      (na: Encoded) => mkSubstituter(Map(aT -> na))(encoded)
    })

    def apply(dtpe: Type, containerType: FunctionType): CaptureTemplate = cache.getOrElseUpdate(dtpe -> containerType, {
      val (ps, ids, condVars, exprVars, condTree, clauses, types, funs) = tmplCache.getOrElseUpdate(dtpe, {
        object b extends { val tpe = dtpe } with super[FunctionUnrolling].Builder with super[ADTUnrolling].Builder
        assert(b.calls.isEmpty, "Captured function templates shouldn't have any calls: " + b.calls)
        (b.pathVar -> b.pathVarT, b.v -> b.idT, b.conds, b.exprs, b.tree, b.clauses, b.types, b.funs)
      })

      val ctpe = bestRealType(containerType).asInstanceOf[FunctionType]
      val container = Variable.fresh("container", ctpe, true)
      val containerT = encodeSymbol(container)

      val typeBlockers: TypeBlockers = types.map { case (blocker, tps) =>
        blocker -> tps.map { case (info, arg) => TemplateTypeInfo(info, arg, Capture(containerT, ctpe)) }
      }

      val orderClauses = funs.map { case (blocker, tpe, f) =>
        mkImplies(blocker, lessThan(order(tpe)(f), order(ctpe)(containerT)))
      }

      new CaptureTemplate(TemplateContents(
        ps, Seq(container -> containerT, ids),
        condVars, exprVars, Map.empty, condTree, clauses ++ orderClauses,
        Map.empty, Map.empty, Map.empty, Map.empty, Seq.empty, Seq.empty, Map.empty
      ), typeBlockers, funs.map(_._3))
    })
  }

  /** Template used to unfold adts returned from functions or maps. */
  class InvariantTemplate private[DatatypeTemplates] (
    val contents: TemplateContents,
    val types: Map[Encoded, Set[TemplateTypeInfo]]) extends TypesTemplate {

    def instantiate(blocker: Encoded, arg: Encoded): Clauses = {
      instantiate(blocker, Seq(Left(arg)))
    }
  }

  /** Extends [[TemplateGenerator]] with functionalities for checking whether
    * tuples need to be unrolled. This trait will typically be mixed in with
    * the [[ADTUnrolling]] trait. */
  trait FlatUnrolling extends TemplateGenerator {
    def unroll(tpe: Type): Boolean = tpe match {
      case TupleType(tps) => tps.exists(unroll)
      case _ => false
    }
  }

  /** Template generator for [[InvariantTemplate]] instances. */
  object InvariantTemplate extends TemplateGenerator with FlatUnrolling with InvariantGenerator {
    private val cache: MutableMap[Type, InvariantTemplate] = MutableMap.empty

    def apply(dtpe: Type): InvariantTemplate = cache.getOrElseUpdate(dtpe, {
      object b extends { val tpe = dtpe } with Builder
      val typeBlockers: TypeBlockers = b.types.map { case (blocker, tps) =>
        blocker -> tps.map { case (info, arg) => TemplateTypeInfo(info, arg, Invariant) }
      }

      new InvariantTemplate(TemplateContents(
        b.pathVar -> b.pathVarT, Seq(b.v -> b.idT),
        b.conds, b.exprs, Map.empty, b.tree, b.clauses, b.calls,
        Map.empty, Map.empty, Map.empty, Seq.empty, Seq.empty, Map.empty
      ), typeBlockers)
    })
  }

  private[unrolling] object datatypesManager extends Manager {
    private[DatatypeTemplates] val typeInfos = new IncrementalMap[Encoded, (Int, Int, Encoded, Set[TemplateTypeInfo])]
    private[DatatypeTemplates] val lessOrder = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)

    def canEqual(f1: Encoded, f2: Encoded): Boolean = {
      def transitiveLess(l: Encoded, r: Encoded): Boolean = {
        val fs = fixpoint((fs: Set[Encoded]) => fs ++ fs.flatMap(lessOrder))(lessOrder(l))
        fs(r)
      }

      !transitiveLess(f1, f2) && !transitiveLess(f2, f1)
    }

    val incrementals: Seq[IncrementalState] = Seq(typeInfos, lessOrder)

    def unrollGeneration: Option[Int] =
      if (typeInfos.isEmpty) None
      else Some(typeInfos.values.map(_._1).min)

    def satisfactionAssumptions: Seq[Encoded] = typeInfos.map(_._2._3).toSeq
    def refutationAssumptions: Seq[Encoded] = Seq.empty

    def promoteBlocker(b: Encoded): Boolean = {
      if (typeInfos contains b) {
        val (_, origGen, notB, tps) = typeInfos(b)
        typeInfos += b -> (currentGeneration, origGen, notB, tps)
        true
      } else {
        false
      }
    }

    def unroll: Clauses = if (typeInfos.isEmpty) Seq.empty else {
      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val typeBlockers = typeInfos.filter(_._2._1 <= currentGeneration).toSeq.map(_._1)
      val newTypeInfos = typeBlockers.flatMap(id => typeInfos.get(id).map(id -> _))
      typeInfos --= typeBlockers

      for ((blocker, (gen, _, _, tps)) <- newTypeInfos; TemplateTypeInfo(info, arg, inst) <- tps) inst match {
        case Datatype =>
          val template = DatatypeTemplate(info.getType)
          newClauses ++= template.instantiate(blocker, arg)
        case Capture(container, containerType) =>
          val template = CaptureTemplate(info.getType, containerType)
          newClauses ++= template.instantiate(blocker, container, arg)
        case Invariant =>
          val template = InvariantTemplate(info.getType)
          newClauses ++= template.instantiate(blocker, arg)
      }

      ctx.reporter.debug("Unrolling datatypes (" + newClauses.size + ")")
      for (cl <- newClauses) {
        ctx.reporter.debug("  . " + cl)
      }

      newClauses.toSeq
    }
  }
}
