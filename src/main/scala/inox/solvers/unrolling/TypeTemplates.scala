/* Copyright 2009-2018 EPFL, Lausanne */

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
trait TypeTemplates { self: Templates =>
  import context._
  import program._
  import program.trees._
  import program.symbols._

  import typesManager._

  /** Determines whether a given type should be unrolled, depending on the kind of type unrolling,
    * namely free variable type unrolling (dependent types and ADT invariants), contract
    * type unrolling (dependent types), and capture unrolling (function closure ordering). */
  protected sealed abstract class TypeUnrolling {
    private[this] val unrollCache: MutableMap[TypedADTSort, Boolean] = MutableMap.empty

    def unroll(tpe: Type): Boolean = tpe match {
      case adt: ADTType =>
        val sort = adt.getSort
        (this == FreeUnrolling && sort.invariant.nonEmpty) ||
        (unrollCache.get(sort) match {
          case Some(b) => b
          case None =>
            unrollCache(sort) = false
            val res = sort.constructors.exists(c => c.fields.exists(vd => unroll(vd.tpe)))
            unrollCache(sort) = res
            res
        })

      case (_: BagType | _: SetType) if this != ContractUnrolling => true
      case FunctionType(_, to) => this != ContractUnrolling || unroll(to)
      case PiType(_, to) => this != ContractUnrolling || unroll(to)
      case RefinementType(vd, _) => this != CaptureUnrolling || unroll(vd.tpe)
      case SigmaType(params, to) => params.exists(vd => unroll(vd.tpe)) || unroll(to)
      case tp: TypeParameter => this == FreeUnrolling
      case NAryType(tpes, _) => tpes.exists(unroll)
    }
  }

  protected case object FreeUnrolling extends TypeUnrolling
  protected case object ContractUnrolling extends TypeUnrolling
  protected case object CaptureUnrolling extends TypeUnrolling


  protected sealed abstract class TypingGenerator(unrolling: TypeUnrolling) {
    def unroll(tpe: Type): Boolean = unrolling unroll tpe
  }

  protected case object FreeGenerator extends TypingGenerator(FreeUnrolling)
  protected case object ContractGenerator extends TypingGenerator(ContractUnrolling)
  protected case class CaptureGenerator(container: Encoded, tpe: FunctionType)
    extends TypingGenerator(ContractUnrolling)


  /** Represents the kind of instantiator (@see [[TypesTemplate]]) a given
    * template info is associated to. */
  sealed abstract class TemplateInstantiator {
    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): TemplateInstantiator
  }

  case class Constraint(result: Encoded, closures: Seq[Arg], free: Boolean) extends TemplateInstantiator {
    override def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): TemplateInstantiator =
      Constraint(substituter(result), closures map (_.substitute(substituter, msubst)), free)
  }

  case class Capture(encoded: Encoded, tpe: FunctionType) extends TemplateInstantiator {
    override def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): TemplateInstantiator =
      Capture(substituter(encoded), tpe)
  }


  /** Represents a type unfolding of a free variable (or input) in the unfolding procedure */
  case class Typing(tpe: Type, arg: Encoded, instantiator: TemplateInstantiator) {
    override def toString: String =
      tpe.asString + "(" + asString(arg) + ")" + (instantiator match {
        case Capture(f, tpe) => " in " + asString(f)
        case _ => ""
      })

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Typing = copy(
      arg = substituter(arg),
      instantiator = instantiator.substitute(substituter, msubst)
    )

    def unroll: Boolean = instantiator match {
      case Constraint(_, _, free) => (if (free) FreeUnrolling else ContractUnrolling) unroll tpe
      case Capture(_, _) => CaptureUnrolling unroll tpe
    }
  }

  /** Sets up the relevant unfolding procedure for closure ordering */
  def registerClosure(start: Encoded, container: (Encoded, FunctionType), arg: (Encoded, Type)): Clauses = {
    CaptureTemplate(arg._2, container._2).instantiate(start, container._1, arg._1)
  }

  private[this] def instantiateTyping(blocker: Encoded, typing: Typing): Clauses = typing match {
    case Typing(tpe, arg, Constraint(result, closures, free)) => tpe match {
      case (_: FunctionType | _: PiType) =>
        registerFunction(blocker, result, tpe, arg, closures, free)
      case _ =>
        ConstraintTemplate(tpe, free).instantiate(blocker, result, arg, closures)
    }
    case Typing(tpe, arg, Capture(container, containerType)) =>
      CaptureTemplate(tpe, containerType).instantiate(blocker, container, arg)
  }

  def instantiateType(blocker: Encoded, typing: Typing): Clauses = typing.tpe match {
    // If no unrolling is necessary, we don't need to register this typing
    case _ if !typing.unroll =>
      typing.instantiator match {
        case Constraint(res, _, _) => Seq(mkImplies(blocker, mkEquals(res, trueT)))
        case _ => Seq.empty
      }

    // In certain non-recursive cases, we want to instantiate the typing
    // immediately to improve unrolling performance
    case (_: FunctionType | _: PiType) => instantiateTyping(blocker, typing)
    case (_: TypeParameter) => instantiateTyping(blocker, typing)
    case adt: ADTType if !adt.getSort.definition.isInductive => instantiateTyping(blocker, typing)

    // In the default case, we simply register the typing for unrolling at
    // a later generation.
    case _ =>
      val gen = nextGeneration(currentGeneration)
      val notBlocker = mkNot(blocker)

      typeInfos.get(blocker) match {
        case Some((exGen, origGen, _, exTps)) =>
          val minGen = gen min exGen
          typeInfos += blocker -> (minGen, origGen, notBlocker, exTps + typing)
        case None =>
          typeInfos += blocker -> (gen, gen, notBlocker, Set(typing))
      }

      Seq.empty
  }

  /** Template used to unfold free symbols in the input expression. */
  class ConstraintTemplate private[TypeTemplates] (val contents: TemplateContents) extends Template {
    def instantiate(blocker: Encoded, result: Encoded, arg: Encoded, closures: Seq[Arg]): Clauses = {
      instantiate(blocker, Seq(Left(result), Left(arg)) ++ closures)
    }
  }

  /** Generator for [[ConstraintTemplate]] instances. */
  object ConstraintTemplate {
    private val cache: MutableMap[(Type, Boolean), ConstraintTemplate] = MutableMap.empty

    def apply(tpe: Type, free: Boolean): ConstraintTemplate = cache.getOrElseUpdate(tpe -> free, {
      val v = Variable.fresh("x", tpe.getType, true)
      val pathVar = Variable.fresh("b", BooleanType(), true)
      val result = Variable.fresh("result", BooleanType(), true)
      val (idT, pathVarT, resultT) = (encodeSymbol(v), encodeSymbol(pathVar), encodeSymbol(result))

      val arguments = typeOps.variablesOf(tpe).toSeq.sortBy(_.id).map(v => v -> encodeSymbol(v))

      val substMap = Map(v -> idT, pathVar -> pathVarT) ++ arguments

      implicit val generator = if (free) FreeGenerator else ContractGenerator
      val (p, tmplClauses) = mkTypeClauses(pathVar, tpe, v, substMap)
      val (contents, _) = Template.contents(
        pathVar -> pathVarT, Seq(result -> resultT, v -> idT) ++ arguments,
        tmplClauses + (pathVar -> Equals(result, p)))

      new ConstraintTemplate(contents)
    })
  }

  /** Template used to unfold ADT closures that may contain functions. */
  class CaptureTemplate private[TypeTemplates](
    val contents: TemplateContents, val functions: Set[Encoded]) extends Template {

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
  object CaptureTemplate {

    private val cache: MutableMap[(Type, FunctionType), CaptureTemplate] = MutableMap.empty
    private val ordCache: MutableMap[FunctionType, Encoded => Encoded] = MutableMap.empty

    private val lessThan: (Encoded, Encoded) => Encoded = {
      val l = Variable.fresh("left", IntegerType())
      val r = Variable.fresh("right", IntegerType())
      val (lT, rT) = (encodeSymbol(l), encodeSymbol(r))

      val encoded = mkEncoder(Map(l -> lT, r -> rT))(LessThan(l, r))
      (nl: Encoded, nr: Encoded) => mkSubstituter(Map(lT -> nl, rT -> nr))(encoded)
    }

    private def order(tpe: FunctionType): Encoded => Encoded = ordCache.getOrElseUpdate(tpe, {
      val a = Variable.fresh("arg", tpe)
      val o = Variable.fresh("order", FunctionType(Seq(tpe), IntegerType()), true)
      val (aT, oT) = (encodeSymbol(a), encodeSymbol(o))
      val encoded = mkEncoder(Map(a -> aT, o -> oT))(Application(o, Seq(a)))
      (na: Encoded) => mkSubstituter(Map(aT -> na))(encoded)
    })

    def apply(tpe: Type, containerType: FunctionType): CaptureTemplate = cache.getOrElseUpdate(tpe -> containerType, {
      val v = Variable.fresh("x", tpe.getType, true)
      val pathVar = Variable.fresh("b", BooleanType(), true)
      val (idT, pathVarT) = (encodeSymbol(v), encodeSymbol(pathVar))

      val substMap = Map(v -> idT, pathVar -> pathVarT)

      val container = Variable.fresh("container", containerType, true)
      val containerT = encodeSymbol(container)

      implicit val generator = CaptureGenerator(containerT, containerType)
      val (p, tmplClauses) = mkTypeClauses(pathVar, tpe, v, substMap)
      val (condVars, exprVars, _, _, _, types, equalities, lambdas, quants) = tmplClauses
      assert(equalities.isEmpty && lambdas.isEmpty && quants.isEmpty,
        "Unexpected complex template clauses in capture template")

      val (contents, _) = Template.contents(
        pathVar -> pathVarT, Seq(v -> idT), tmplClauses + (pathVar -> p))

      val fullSubst = substMap ++ condVars ++ exprVars

      val encoder: Expr => Encoded = mkEncoder(fullSubst)

      var typeBlockers: Types = Map.empty
      var funClauses: Clauses = Seq.empty
      var functions: Set[Encoded] = Set.empty

      for ((b, tps) <- types; tp <- tps) tp match {
        case Typing(ft: FunctionType, arg, Capture(containerT, containerType)) =>
          funClauses :+= mkImplies(b, lessThan(order(ft)(arg), order(containerType)(containerT)))
          functions += arg
        case _ => typeBlockers += b -> (typeBlockers.getOrElse(b, Set.empty) + tp)
      }

      new CaptureTemplate(contents.copy(
        arguments = (container -> containerT) +: contents.arguments,
        clauses = contents.clauses ++ funClauses,
        types = typeBlockers
      ), functions)
    })
  }

  private[unrolling] object typesManager extends Manager {
    private[TypeTemplates] val typeInfos = new IncrementalMap[Encoded, (Int, Int, Encoded, Set[Typing])]
    private[TypeTemplates] val lessOrder = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)
    private[TypeTemplates] val results = new IncrementalMap[(Type, Seq[Arg], Boolean), Encoded]

    private val tpSyms: MutableMap[TypeParameter, Variable] = MutableMap.empty
    private[unrolling] val tpSubst: MutableMap[Variable, Encoded] = MutableMap.empty
    private[unrolling] def storeTypeParameter(tp: TypeParameter): Variable =
      tpSyms.getOrElseUpdate(tp, {
        val v = Variable.fresh("tp_is_empty", BooleanType(), true)
        tpSubst(v) = encodeSymbol(v)
        v
      })

    def canBeEqual(f1: Encoded, f2: Encoded): Boolean = {
      def transitiveLess(l: Encoded, r: Encoded): Boolean = {
        val fs = fixpoint((fs: Set[Encoded]) => fs ++ fs.flatMap(lessOrder))(lessOrder(l))
        fs(r)
      }

      !transitiveLess(f1, f2) && !transitiveLess(f2, f1)
    }

    val incrementals: Seq[IncrementalState] = Seq(typeInfos, lessOrder, results)

    def unrollGeneration: Option[Int] =
      if (typeInfos.isEmpty) None
      else Some(typeInfos.values.map(_._1).min)

    def satisfactionAssumptions: Seq[Encoded] =
      typeInfos.map(_._2._3).toSeq ++ tpSubst.values

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

      for ((blocker, (gen, _, _, tps)) <- newTypeInfos; tp <- tps) {
        newClauses ++= instantiateTyping(blocker, tp)
      }

      reporter.debug("Unrolling types (" + newClauses.size + ")")
      for (cl <- newClauses) {
        reporter.debug("  . " + cl)
      }

      newClauses.toSeq
    }
  }
}
