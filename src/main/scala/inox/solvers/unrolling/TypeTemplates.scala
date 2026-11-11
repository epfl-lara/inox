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
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import typesManager._

  /** Determines whether a given type should be unrolled, depending on the kind of type unrolling,
    * namely free variable type unrolling (dependent types and ADT invariants), contract
    * type unrolling (dependent types), read unrolling (dependent types and ADT invariants, but not
    * what only free values need, see [[Collection]]) and capture unrolling (function closure ordering). */
  protected sealed abstract class TypeUnrolling {
    private val unrollCache: MutableMap[TypedADTSort, Boolean] = MutableMap.empty

    def unroll(tpe: Type): Boolean = tpe match {
      case adt: ADTType =>
        val sort = adt.getSort
        ((this == FreeUnrolling || this == ReadUnrolling) && sort.invariant.nonEmpty) ||
        (unrollCache.get(sort) match {
          case Some(b) => b
          case None =>
            unrollCache(sort) = false
            val res = sort.constructors.exists(c => c.fields.exists(vd => unroll(vd.tpe)))
            unrollCache(sort) = res
            res
        })

      case (_: BagType | _: SetType) if this == FreeUnrolling || this == CaptureUnrolling => true
      case FunctionType(_, to) => this == FreeUnrolling || this == CaptureUnrolling || unroll(to)
      case PiType(_, to) => this == FreeUnrolling || this == CaptureUnrolling || unroll(to)
      case RefinementType(vd, _) => this != CaptureUnrolling || unroll(vd.tpe)
      case SigmaType(params, to) => params.exists(vd => unroll(vd.tpe)) || unroll(to)
      case tp: TypeParameter => this == FreeUnrolling
      case NAryType(tpes, _) => tpes.exists(unroll)
    }
  }

  protected case object FreeUnrolling extends TypeUnrolling
  protected case object ContractUnrolling extends TypeUnrolling
  protected case object CaptureUnrolling extends TypeUnrolling
  protected case object ReadUnrolling extends TypeUnrolling


  protected sealed abstract class TypingGenerator(unrolling: TypeUnrolling) {
    def unroll(tpe: Type): Boolean = unrolling `unroll` tpe
  }

  protected case object FreeGenerator extends TypingGenerator(FreeUnrolling)
  protected case object ContractGenerator extends TypingGenerator(ContractUnrolling)
  /** Generator for checks that must be proven rather than assumed, such as the membership of an
    * argument in the domain of a Pi type (@see [[Membership]]). */
  protected case object MembershipGenerator extends TypingGenerator(ContractUnrolling)
  protected case class CaptureGenerator(container: Encoded, tpe: FunctionType)
    extends TypingGenerator(CaptureUnrolling)


  /** Represents the kind of instantiator (@see [[ConstraintTemplate]] and [[CaptureTemplate]]) a given
    * template info is associated to. */
  sealed abstract class TemplateInstantiator {
    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): TemplateInstantiator
  }

  /** @param inDomain whether the type check belongs to a quantifier's domain
    *                 (see `TemplateGenerator.mkTypeClauses`) */
  case class Constraint(result: Encoded, closures: Seq[Arg], free: Boolean, inDomain: Boolean = false)
    extends TemplateInstantiator {
    override def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): TemplateInstantiator =
      Constraint(substituter(result), closures map (_.substitute(substituter, msubst)), free, inDomain)
  }

  /** Checks whether a value lies in a type, where the result must be exact in models and may only be
    * false in proofs if the value lies outside of the type.
    *
    * [[Constraint]] typings only check the applications of functions that appear in the formula, so
    * an unapplied function such as `x => -1` would lie in `Pi(x: BigInt). {r | r > 0}`. This is
    * sound for typings that are assumed, but not for typings that must be proven. Membership
    * typings instead check functions at fresh arguments: `f` lies in `Pi(x: A). B` iff
    * `A(x0) ==> B(f(x0))` for all `x0`, and the solver may pick `x0` as a counterexample.
    * (@see [[TemplateGenerator.mkTypeClauses]]) */
  case class Membership(result: Encoded, closures: Seq[Arg]) extends TemplateInstantiator {
    override def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): TemplateInstantiator =
      Membership(substituter(result), closures map (_.substitute(substituter, msubst)))
  }

  /** Types the reads of a free map, set or bag: the values of a map at the keys and the elements of a
    * set or bag that the formula reads (@see [[registerCollection]]), similarly to how free functions
    * are typed at their applications. The decomposition of the collection only types the elements
    * it unfolds, which don't include arbitrary reads such as `m(k)` for a free key `k`.
    *
    * Free collections (`free`) are typed at every read of their type that may read them. The
    * results of contracts are only typed at the reads of the same term, similarly to applications
    * of known lambdas, which aren't dispatched to the other functions of their type: these results
    * may be many (e.g. the contents of lists in Stainless), and pairing each of them with every read
    * of their type makes the unrolling quadratic. */
  case class Collection(result: Encoded, closures: Seq[Arg], free: Boolean) extends TemplateInstantiator {
    override def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): TemplateInstantiator =
      Collection(substituter(result), closures map (_.substitute(substituter, msubst)), free)
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
      case Constraint(_, _, free, _) => (if (free) FreeUnrolling else ContractUnrolling) `unroll` tpe
      case Membership(_, _) => ContractUnrolling `unroll` tpe
      case Collection(_, _, free) => (if (free) FreeUnrolling else ContractUnrolling) `unroll` tpe
      case Capture(_, _) => CaptureUnrolling `unroll` tpe
    }
  }

  /** Sets up the relevant unfolding procedure for closure ordering */
  def registerClosure(start: Encoded, container: (Encoded, FunctionType), arg: (Encoded, Type)): Clauses = {
    CaptureTemplate(arg._2, container._2).instantiate(start, container._1, arg._1)
  }

  private def instantiateTyping(blocker: Encoded, typing: Typing): Clauses = {
    // The clauses of a typing are guarded by the blocker it is instantiated under, so its result
    // is only shared under the same blocker: it would be unconstrained elsewhere, and could then be
    // set to drop an assumption, or to accept a value that doesn't belong to the type.
    def cached(tpe: Type, arg: Encoded, closures: Seq[Arg], generator: TypingGenerator, inDomain: Boolean, result: Encoded)
              (instantiate: => Clauses): Clauses = {
      val key = (tpe, arg, closures, generator, inDomain, blocker)
      results.get(key) match {
        case Some(res) => Seq(mkEquals(result, res))
        case None =>
          results += key -> result
          instantiate
      }
    }

    typing match {
      case Typing(tpe, arg, Membership(result, closures)) =>
        // Membership must be fully constrained, like the domain of a quantifier (see `inDomain`).
        cached(tpe, arg, closures, MembershipGenerator, true, result) {
          ConstraintTemplate(tpe, MembershipGenerator, true).instantiate(blocker, result, arg, closures)
        }

      case Typing(tpe, arg, Constraint(result, closures, free, inDomain)) =>
        val generator = if (free) FreeGenerator else ContractGenerator
        cached(tpe, arg, closures, generator, inDomain, result) {
          tpe match {
            case (_: FunctionType | _: PiType) =>
              registerFunction(blocker, result, tpe, arg, closures, free)
            case _ =>
              ConstraintTemplate(tpe, generator, inDomain).instantiate(blocker, result, arg, closures)
          }
        }

      case Typing(tpe, arg, Collection(result, closures, free)) =>
        registerCollection(blocker, result, tpe, arg, closures, free)

      case Typing(tpe, arg, Capture(container, containerType)) =>
        CaptureTemplate(tpe, containerType).instantiate(blocker, container, arg)
    }
  }

  /** The element type of a collection, and the read of the collection at `key` as the condition under
    * which the read is defined and the value it reads. */
  private def collectionRead(tpe: Type, collection: Encoded, key: Encoded): (Type, Encoded, Encoded) = {
    val c = Variable.fresh("c", tpe.getType, true)
    tpe match {
      case MapType(from, to) =>
        val k = Variable.fresh("k", from.getType, true)
        val encoder = mkEncoder(Map(c -> collection, k -> key))
        (to, trueT, encoder(MapApply(c, k)))
      case SetType(base) =>
        val k = Variable.fresh("k", base.getType, true)
        (base, mkEncoder(Map(c -> collection, k -> key))(ElementOfSet(k, c)), key)
      case BagType(base) =>
        val k = Variable.fresh("k", base.getType, true)
        val encoder = mkEncoder(Map(c -> collection, k -> key))
        (base, encoder(GreaterThan(MultiplicityInBag(k, c), IntegerLiteral(0))), key)
      case _ => throw new InternalSolverError("Unexpected collection type: " + tpe.asString)
    }
  }

  /** Adds the typing of the read of `collection` at `key` to the reads typing of `collection`
    * (@see [[Collection]]): the read lies in the element type when `readBlocker` holds and the
    * collection equals the read one. As for the applications of free functions, the typing
    * result is a conjunction over the reads, which is extended with every new read. */
  private def typeRead(info: CollectionInfo, readBlocker: Encoded, read: Encoded, key: Encoded): Clauses = {
    val CollectionInfo(blocker, tpe, collection, closures, next, free) = info
    if (typesManager.readTypings `contains` ((blocker, collection, read, key))) Seq.empty else {
      val (elemTpe, cond, value) = collectionRead(tpe, collection, key)
      val guard = mkAnd(readBlocker, mkEquals(collection, read), cond)
      val typeBlocker = encodeSymbol(Variable.fresh("rb", BooleanType(), true))
      val result = encodeSymbol(Variable.fresh("result", BooleanType(), true))
      val nextB = encodeSymbol(Variable.fresh("r_and", BooleanType(), true))
      typesManager.readTypings += (blocker, collection, read, key) -> nextB
      typesManager.collectionNexts += next -> nextB

      val subst: Map[Variable, Arg] = (typeOps.variablesOf(tpe).toSeq.sortBy(_.id) zip closures).toMap
      val elemClosures = typeOps.variablesOf(elemTpe).toSeq.sortBy(_.id).map(subst)

      registerImplication(blocker, typeBlocker)
      Seq(
        mkImplies(mkAnd(blocker, guard), typeBlocker),
        mkImplies(blocker, mkEquals(next, mkAnd(mkImplies(guard, result), nextB)))
      ) ++ instantiateType(typeBlocker, Typing(elemTpe, value, Constraint(result, elemClosures, free)))
    }
  }

  /** Registers the collection `collection` of type `tpe`, whose reads are typed when the
    * collection may equal the read collection, if it is free, and when the read collection is
    * `collection` itself otherwise (@see [[Collection]]). */
  def registerCollection(blocker: Encoded, result: Encoded, tpe: Type, collection: Encoded, closures: Seq[Arg],
                         free: Boolean): Clauses = {
    val ct = tpe.getType
    val info = CollectionInfo(blocker, tpe, collection, closures, result, free)
    if (free) {
      typesManager.collections += ct -> (typesManager.collections(ct) + info)
      typesManager.reads(ct).toSeq.flatMap { case (readBlocker, read, key) =>
        typeRead(info.current, readBlocker, read, key)
      }
    } else {
      typesManager.boundCollections += collection -> (typesManager.boundCollections(collection) + info)
      typesManager.readsOf(collection).toSeq.flatMap { case (readBlocker, key) =>
        typeRead(info.current, readBlocker, collection, key)
      }
    }
  }

  /** Instantiates a read of a collection under `blocker` (@see [[Read]]). Every read is
    * registered once, under its own read blocker, and typed for the free collections it may equal
    * (@see [[registerCollection]]). */
  def instantiateRead(blocker: Encoded, read: Read): Clauses = {
    val Read(tpe, collection, key) = read
    val ct = tpe.getType
    val (readBlocker, readClauses) = typesManager.readBlockers.get((collection, key)) match {
      case Some(readBlocker) => (readBlocker, Seq.empty)
      case None =>
        val readBlocker = encodeSymbol(Variable.fresh("rd", BooleanType(), true))
        typesManager.readBlockers += (collection, key) -> readBlocker
        typesManager.reads += ct -> (typesManager.reads(ct) + ((readBlocker, collection, key)))
        typesManager.readsOf += collection -> (typesManager.readsOf(collection) + (readBlocker -> key))
        val infos = typesManager.collections(ct).toSeq ++ typesManager.boundCollections(collection)
        (readBlocker, infos.flatMap(info => typeRead(info.current, readBlocker, collection, key)))
    }

    registerImplication(blocker, readBlocker)
    readClauses :+ mkImplies(blocker, readBlocker)
  }

  /** A collection, whose reads typing so far ends with the `next` literal. */
  private case class CollectionInfo(blocker: Encoded, tpe: Type, collection: Encoded, closures: Seq[Arg], next: Encoded,
                                    free: Boolean) {
    def current: CollectionInfo = {
      var n = next
      while (typesManager.collectionNexts `contains` n) n = typesManager.collectionNexts(n)
      copy(next = n)
    }
  }

  def instantiateType(blocker: Encoded, typing: Typing): Clauses = typing.tpe match {
    // If no unrolling is necessary, we don't need to register this typing
    case _ if !typing.unroll =>
      typing.instantiator match {
        case Constraint(res, _, _, _) => Seq(mkImplies(blocker, mkEquals(res, trueT)))
        case Membership(res, _) => Seq(mkImplies(blocker, mkEquals(res, trueT)))
        case Collection(res, _, _) => Seq(mkImplies(blocker, mkEquals(res, trueT)))
        case _ => Seq.empty
      }

    // In certain non-recursive cases, we want to instantiate the typing
    // immediately to improve unrolling performance
    case (_: FunctionType | _: PiType) => instantiateTyping(blocker, typing)
    case _ if typing.instantiator.isInstanceOf[Collection] => instantiateTyping(blocker, typing)
    case (_: TypeParameter) => instantiateTyping(blocker, typing)
    case adt: ADTType if !adt.getSort.definition.isInductive => instantiateTyping(blocker, typing)

    // In the default case, we simply register the typing for unrolling at
    // a later generation.
    case _ =>
      val gen = nextGeneration(currentGeneration)
      val notBlocker = mkNot(blocker)

      // keep track of the witness depth until the typing is unrolled (see [[LambdaTemplates]])
      if (witnessDepth > 0) typeDepths += blocker -> (witnessDepth max typeDepths.getOrElse(blocker, 0))

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
    private val cache: MutableMap[(Type, TypingGenerator, Boolean), ConstraintTemplate] = MutableMap.empty

    def apply(tpe: Type, generator: TypingGenerator, inDomain: Boolean): ConstraintTemplate =
      cache.getOrElse((tpe, generator, inDomain), {
      val v = Variable.fresh("x", tpe.getType, true)
      val pathVar = Variable.fresh("b", BooleanType(), true)
      val result = Variable.fresh("result", BooleanType(), true)
      val (idT, pathVarT, resultT) = (encodeSymbol(v), encodeSymbol(pathVar), encodeSymbol(result))

      val arguments = typeOps.variablesOf(tpe).toSeq.sortBy(_.id).map(v => v -> encodeSymbol(v))

      val substMap = Map(v -> idT, pathVar -> pathVarT) ++ arguments

      val (p, tmplClauses) = mkTypeClauses(pathVar, tpe, v, substMap, inDomain)(using generator)
      val (contents, _) = Template.contents(
        pathVar -> pathVarT, Seq(result -> resultT, v -> idT) ++ arguments,
        tmplClauses + (pathVar -> Equals(result, p)))

      val res = new ConstraintTemplate(contents)
      cache((tpe, generator, inDomain)) = res
      res
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
      val substituter = mkSubstituter(substMap.view.mapValues(_.encoded).toMap)

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

    private def order(tpe: FunctionType): Encoded => Encoded = ordCache.getOrElse(tpe, {
      val a = Variable.fresh("arg", tpe)
      val o = Variable.fresh("order", FunctionType(Seq(tpe), IntegerType()), true)
      val (aT, oT) = (encodeSymbol(a), encodeSymbol(o))
      val encoded = mkEncoder(Map(a -> aT, o -> oT))(Application(o, Seq(a)))
      val res = (na: Encoded) => mkSubstituter(Map(aT -> na))(encoded)
      ordCache(tpe) = res
      res
    })

    def apply(tpe: Type, containerType: FunctionType): CaptureTemplate = cache.getOrElse(tpe -> containerType, {
      val v = Variable.fresh("x", tpe.getType, true)
      val pathVar = Variable.fresh("b", BooleanType(), true)
      val (idT, pathVarT) = (encodeSymbol(v), encodeSymbol(pathVar))

      val substMap = Map(v -> idT, pathVar -> pathVarT)

      val container = Variable.fresh("container", containerType, true)
      val containerT = encodeSymbol(container)

      given CaptureGenerator = CaptureGenerator(containerT, containerType)
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
        case Typing(t @ (_: FunctionType | _: PiType), arg, Capture(containerT, containerType)) =>
          val ft = t.getType.asInstanceOf[FunctionType]
          funClauses :+= mkImplies(b, lessThan(order(ft)(arg), order(containerType)(containerT)))
          functions += arg
        case _ => typeBlockers += b -> (typeBlockers.getOrElse(b, Set.empty) + tp)
      }

      val res = new CaptureTemplate(contents.copy(
        arguments = (container -> containerT) +: contents.arguments,
        clauses = contents.clauses ++ funClauses,
        types = typeBlockers
      ), functions)

      cache(tpe -> containerType) = res
      res
    })
  }

  private[unrolling] object typesManager extends Manager {
    private[TypeTemplates] val typeInfos = new IncrementalMap[Encoded, (Int, Int, Encoded, Set[Typing])]
    private[TypeTemplates] val lessOrder = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)
    private[TypeTemplates] val results = new IncrementalMap[(Type, Encoded, Seq[Arg], TypingGenerator, Boolean, Encoded), Encoded]
    private[TypeTemplates] val typeDepths = new IncrementalMap[Encoded, Int]

    private val tpSyms: MutableMap[TypeParameter, Variable] = MutableMap.empty
    private[unrolling] val tpSubst: MutableMap[Variable, Encoded] = MutableMap.empty
    private[unrolling] def storeTypeParameter(tp: TypeParameter): Variable =
      tpSyms.getOrElse(tp, {
        val v = Variable.fresh("tp_is_empty", BooleanType(), true)
        tpSubst(v) = encodeSymbol(v)
        tpSyms(tp) = v
        v
      })

    def canBeEqual(f1: Encoded, f2: Encoded): Boolean = {
      def transitiveLess(l: Encoded, r: Encoded): Boolean = {
        val fs = fixpoint((fs: Set[Encoded]) => fs ++ fs.flatMap(lessOrder))(lessOrder(l))
        fs(r)
      }

      !transitiveLess(f1, f2) && !transitiveLess(f2, f1)
    }

    private[TypeTemplates] val collections =
      new IncrementalMap[Type, Set[CollectionInfo]].withDefaultValue(Set.empty)
    private[TypeTemplates] val boundCollections =
      new IncrementalMap[Encoded, Set[CollectionInfo]].withDefaultValue(Set.empty)
    private[TypeTemplates] val reads = new IncrementalMap[Type, Set[(Encoded, Encoded, Encoded)]].withDefaultValue(Set.empty)
    private[TypeTemplates] val readsOf = new IncrementalMap[Encoded, Set[(Encoded, Encoded)]].withDefaultValue(Set.empty)
    private[TypeTemplates] val readBlockers = new IncrementalMap[(Encoded, Encoded), Encoded]
    private[TypeTemplates] val readTypings = new IncrementalMap[(Encoded, Encoded, Encoded, Encoded), Encoded]
    private[TypeTemplates] val collectionNexts = new IncrementalMap[Encoded, Encoded]

    val incrementals: Seq[IncrementalState] =
      Seq(typeInfos, lessOrder, results, typeDepths, collections, boundCollections, reads, readsOf,
        readBlockers, readTypings, collectionNexts)

    def unrollGeneration: Option[Int] =
      if (typeInfos.isEmpty) None
      else Some(typeInfos.values.map(_._1).min)

    /** The last literal of the reads typing of each free collection, which is assumed to hold as
      * the reads that are yet to come extend it (@see [[registerCollection]]), similarly to the
      * typing blockers of free functions in [[LambdaTemplates]]. */
    private def readsTails: Seq[Encoded] =
      (collections.toSeq ++ boundCollections.toSeq).flatMap(_._2.map(_.current.next))

    def satisfactionAssumptions: Seq[Encoded] =
      typeInfos.map(_._2._3).toSeq ++ tpSubst.values ++ readsTails

    def refutationAssumptions: Seq[Encoded] = readsTails

    def promoteBlocker(b: Encoded): Boolean = {
      if (typeInfos `contains` b) {
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
        newClauses ++= withWitnessDepth(typeDepths.getOrElse(blocker, 0))(instantiateTyping(blocker, tp))
      }

      reporter.debug("Unrolling types (" + newClauses.size + ")")
      for (cl <- newClauses) {
        reporter.debug("  . " + cl)
      }

      newClauses.toSeq
    }
  }
}
