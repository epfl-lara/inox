/* Copyright 2009-2015 EPFL, Lausanne */

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

  /** Represents a type unfolding of a free variable (or input) in the unfolding procedure */
  case class TemplateTypeInfo(tsort: TypedADTSort, arg: Encoded, outer: Option[(Encoded, FunctionType)]) {
    override def toString: String =
      tsort.toType.asString + "(" + asString(arg) + ")" + (outer match {
        case Some((f, tpe)) => " in " + asString(f)
        case None => ""
      })

    def substitute(substituter: Encoded => Encoded): TemplateTypeInfo = copy(
      arg = substituter(arg),
      outer = outer.map(p => (substituter(p._1), p._2))
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

  /** Base trait for datatype unfolding template generators.
    *
    * This trait provides a useful interface for building datatype unfolding
    * templates. The interesting override points are:
    *
    * - [[unrollType]]:
    *   determines whether a given type requires unfolding.
    *   @see [[$DatatypeTemplate.unrollType]]
    *   @see [[$CaptureTemplate.unrollType]]
    *
    * - [[Builder.rec]]:
    *   can be overriden to provide finer controll of what clauses should be generated during
    *   template construction. The [[Builder]] class itself can't be overriden, so one must be
    *   careful to use the overriding class when construction a template! We use a [[Builder]]
    *   class here so that the [[Builder.rec]] method can refer to the current [[Builder]]
    *   state while still providing an override point.
    *   @see [[$DatatypeTemplate.Builder.rec]]
    *   @see [[$CaptureTemplate.Builder.rec]]
    *
    * @see [[$DatatypeTemplate]]
    * @see [[$CaptureTemplate]]
    */
  sealed protected trait TemplateGenerator {
    private val checking: MutableSet[TypedADTDefinition] = MutableSet.empty
    private val unrollCache: MutableMap[Type, Boolean] = MutableMap.empty

    /** Determines whether a given [[Type]] needs to be considered during ADT unfolding.
      * 
      * This function DOES NOT correspond to an override point (hence the `final` modifier.
      * One should look at [[unrollType]] to change the behavior of [[unroll]].
      */
    final def unroll(tpe: Type): Boolean = unrollCache.getOrElseUpdate(tpe, {
      unrollType(tpe) || (tpe match {
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

        case BooleanType | UnitType | CharType | IntegerType |
             RealType | StringType | (_: BVType) | (_: TypeParameter) => false

        case ft: FunctionType => true

        case NAryType(tpes, _) => tpes.exists(unroll)
      })
    })

    /** Override point to determine whether a given type should be unfolded.
      *
      * This methods shouldn't be recursive as the ADT traversal already takes place
      * within the [[unroll]] method.
      *
      * By default, returns `false`.
      */
    protected def unrollType(tpe: Type): Boolean = false

    /** Stateful template generating class. Provides the [[rec]] override point so that
      * subclasses of [[TemplateGenerator]] can override [[rec]] while still using
      * stateful clause generation.
      */
    protected class Builder(tpe: Type) {
      protected val v = Variable(FreshIdentifier("x", true), tpe)
      val pathVar = Variable(FreshIdentifier("b", true), BooleanType)
      val (idT, pathVarT) = (encodeSymbol(v), encodeSymbol(pathVar))

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

      @inline protected def iff(e1: Expr, e2: Expr): Unit = storeGuarded(pathVar, Equals(e1, e2))

      private var tpes = Map[Variable, Set[(TypedADTSort, Expr)]]()
      @inline protected def storeType(pathVar: Variable, tsort: TypedADTSort, arg: Expr): Unit = {
        tpes += pathVar -> (tpes.getOrElse(pathVar, Set.empty) + (tsort -> arg))
      }

      private var functions = Map[Variable, Set[Expr]]()
      @inline protected def storeFunction(pathVar: Variable, expr: Expr): Unit = {
        functions += pathVar -> (functions.getOrElse(pathVar, Set.empty) + expr)
      }

      /** Generates the clauses and other bookkeeping relevant to a type unfolding template.
        * Subtypes of [[Builder]] can override this method to change clause generation. */
      protected def rec(pathVar: Variable, expr: Expr, recurse: Boolean): Unit = expr.getType match {
        case tpe if !unroll(tpe) =>
          // nothing to do here!

        case adt: ADTType =>
          val tadt = adt.getADT

          if (tadt.definition.isSort && tadt.toSort.definition.isInductive && !recurse) {
            storeType(pathVar, tadt.toSort, expr)
          } else {
            val matchers = tadt.root match {
              case (tsort: TypedADTSort) => tsort.constructors
              case (tcons: TypedADTConstructor) => Seq(tcons)
            }

            for (tcons <- matchers) {
              val tpe = tcons.toType

              if (unroll(tpe)) {
                val newBool: Variable = Variable(FreshIdentifier("b", true), BooleanType)
                storeCond(pathVar, newBool)

                for (vd <- tcons.fields) {
                  rec(newBool, ADTSelector(AsInstanceOf(expr, tpe), vd.id), false)
                }

                val vars = tpes.keys.toSet ++ functions.keys ++
                  guardedExprs.flatMap(_._2.flatMap(exprOps.variablesOf))

                if (vars(newBool)) {
                  iff(and(pathVar, IsInstanceOf(expr, tpe)), newBool)
                }
              }
            }
          }

        case TupleType(tpes) =>
          for ((_, idx) <- tpes.zipWithIndex) {
            rec(pathVar, TupleSelect(expr, idx + 1), recurse)
          }

        case FunctionType(_, _) =>
          storeFunction(pathVar, expr)

        case _ => scala.sys.error("TODO")
      }

      /* Calls [[rec]] and finalizes the bookkeeping collection before returning everything
       * necessary to a template creation. */
      lazy val (encoder, conds, tree, clauses, calls, types, funs) = {
        rec(pathVar, v, true)

        val encoder: Expr => Encoded = mkEncoder(condVars + (v -> idT) + (pathVar -> pathVarT))

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

        val encodedTypes: Map[Encoded, Set[(TypedADTSort, Encoded)]] = tpes.map { case (b, tps) =>
          encoder(b) -> tps.map { case (tadt, expr) => (tadt, encoder(expr)) }
        }

        val encodedFunctions: Functions = functions.flatMap { case (b, fs) =>
          val bp = encoder(b)
          fs.map(expr => (bp, bestRealType(expr.getType).asInstanceOf[FunctionType], encoder(expr)))
        }.toSet

        (encoder, condVars, condTree, clauses, calls, encodedTypes, encodedFunctions)
      }
    }
  }

  /** Base type for datatype unfolding templates. */
  trait TypesTemplate extends Template {
    val types: Map[Encoded, Set[TemplateTypeInfo]]

    val exprVars = Map.empty[Variable, Encoded]
    val applications = Map.empty[Encoded, Set[App]]
    val lambdas = Seq.empty[LambdaTemplate]
    val matchers = Map.empty[Encoded, Set[Matcher]]
    val quantifications = Seq.empty[QuantificationTemplate]

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
    val pathVar: (Variable, Encoded),
    val argument: Encoded,
    val condVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: CallBlockers,
    val types: Map[Encoded, Set[TemplateTypeInfo]],
    val functions: Functions) extends TypesTemplate {

    val args = Seq(argument)

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
  object DatatypeTemplate extends TemplateGenerator {
    private val cache: MutableMap[Type, DatatypeTemplate] = MutableMap.empty

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
    protected class Builder(tpe: Type) extends super.Builder(tpe) {
      override protected def rec(pathVar: Variable, expr: Expr, recurse: Boolean): Unit = expr.getType match {
        case adt: ADTType =>
          val tadt = adt.getADT

          if (tadt.hasInvariant) {
            storeGuarded(pathVar, tadt.invariant.get.applied(Seq(expr)))
          }

          if (tadt != tadt.root) {
            storeGuarded(pathVar, IsInstanceOf(expr, tadt.toType))

            val tpe = tadt.toType
            for (vd <- tadt.toConstructor.fields) {
              rec(pathVar, ADTSelector(AsInstanceOf(expr, tpe), vd.id), false)
            }
          } else {
            super.rec(pathVar, expr, recurse)
          }

        case _ => super.rec(pathVar, expr, recurse)
      }
    }

    def apply(tpe: Type): DatatypeTemplate = cache.getOrElseUpdate(tpe, {
      val b = new Builder(tpe)
      val typeBlockers: TypeBlockers = b.types.map { case (blocker, tps) =>
        blocker -> tps.map { case (tadt, arg) => TemplateTypeInfo(tadt, arg, None) }
      }

      new DatatypeTemplate(b.pathVar -> b.pathVarT, b.idT,
        b.conds, b.tree, b.clauses, b.calls, typeBlockers, b.funs)
    })
  }

  /** Template used to unfold ADT closures that may contain functions. */
  class CaptureTemplate private[DatatypeTemplates](
    val pathVar: (Variable, Encoded),
    val container: Encoded,
    val argument: Encoded,
    val condVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val types: Map[Encoded, Set[TemplateTypeInfo]],
    val functions: Set[Encoded]) extends TypesTemplate {

    val args = Seq(container, argument)
    val blockers = Map.empty[Encoded, Set[Call]]

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
  object CaptureTemplate extends TemplateGenerator {
    private val tmplCache: MutableMap[Type, (
      (Variable, Encoded),
      Encoded,
      Map[Variable, Encoded],
      Map[Variable, Set[Variable]],
      Clauses,
      Map[Encoded, Set[(TypedADTSort, Encoded)]],
      Functions
    )] = MutableMap.empty

    private val cache: MutableMap[(Type, FunctionType), CaptureTemplate] = MutableMap.empty
    private val ordCache: MutableMap[FunctionType, Encoded => Encoded] = MutableMap.empty

    private val lessThan: (Encoded, Encoded) => Encoded = {
      val l = Variable(FreshIdentifier("left"), IntegerType)
      val r = Variable(FreshIdentifier("right"), IntegerType)
      val (lT, rT) = (encodeSymbol(l), encodeSymbol(r))

      val encoded = mkEncoder(Map(l -> lT, r -> rT))(LessThan(l, r))
      (nl: Encoded, nr: Encoded) => mkSubstituter(Map(lT -> nl, rT -> nr))(encoded)
    }

    private def order(tpe: FunctionType): Encoded => Encoded = ordCache.getOrElseUpdate(tpe, {
      val a = Variable(FreshIdentifier("arg"), tpe)
      val o = Variable(FreshIdentifier("order", true), FunctionType(Seq(tpe), IntegerType))
      val (aT, oT) = (encodeSymbol(a), encodeSymbol(o))
      val encoded = mkEncoder(Map(a -> aT, o -> oT))(Application(o, Seq(a)))
      (na: Encoded) => mkSubstituter(Map(aT -> na))(encoded)
    })

    def apply(tpe: Type, containerType: FunctionType): CaptureTemplate = cache.getOrElseUpdate(tpe -> containerType, {
      val (ps, idT, condVars, condTree, clauses, types, funs) = tmplCache.getOrElseUpdate(tpe, {
        val b = new Builder(tpe)
        assert(b.calls.isEmpty, "Captured function templates shouldn't have any calls: " + b.calls)
        (b.pathVar -> b.pathVarT, b.idT, b.conds, b.tree, b.clauses, b.types, b.funs)
      })

      val ctpe = bestRealType(containerType).asInstanceOf[FunctionType]
      val container = Variable(FreshIdentifier("container", true), ctpe)
      val containerT = encodeSymbol(container)

      val typeBlockers: TypeBlockers = types.map { case (blocker, tps) =>
        blocker -> tps.map { case (tadt, arg) => TemplateTypeInfo(tadt, arg, Some(containerT -> ctpe)) }
      }

      val orderClauses = funs.map { case (blocker, tpe, f) =>
        mkImplies(blocker, lessThan(order(tpe)(f), order(ctpe)(containerT)))
      }

      new CaptureTemplate(ps, containerT, idT,
        condVars, condTree, clauses ++ orderClauses, typeBlockers, funs.map(_._3))
    })
  }

  private[unrolling] object datatypesManager extends Manager {
    val typeInfos = new IncrementalMap[Encoded, (Int, Int, Encoded, Set[TemplateTypeInfo])]
    val lessOrder = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)

    def canEqual(f1: Encoded, f2: Encoded): Boolean = {
      def transitiveLess(l: Encoded, r: Encoded): Boolean = {
        val fs = fixpoint((fs: Set[Encoded]) => fs ++ fs.flatMap(lessOrder))(Set(l))
        fs(r)
      }

      !transitiveLess(f1, f2) && !transitiveLess(f2, f1)
    }

    val incrementals: Seq[IncrementalState] = Seq(typeInfos)

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

      for ((blocker, (gen, _, _, tps)) <- newTypeInfos; info @ TemplateTypeInfo(tadt, arg, oc) <- tps) oc match {
        case None =>
          val template = DatatypeTemplate(tadt.toType)
          newClauses ++= template.instantiate(blocker, arg)
        case Some((container, containerType)) =>
          val template = CaptureTemplate(tadt.toType, containerType)
          newClauses ++= template.instantiate(blocker, container, arg)
      }

      newClauses.toSeq
    }
  }
}
