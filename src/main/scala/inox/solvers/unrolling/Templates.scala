/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.generic.CanBuildFrom
import scala.collection.mutable.{Set => MutableSet}

trait Templates
  extends TemplateGenerator
     with FunctionTemplates
     with LambdaTemplates
     with QuantificationTemplates
     with EqualityTemplates
     with TypeTemplates
     with WitnessTemplates
     with BlockerGraph
     with PartialFunctions
     with OpenJunctions
     with SolverFacades
     with IncrementalStateWrapper {

  val program: Program
  val context: Context
  protected val semantics: program.Semantics
  given givenSemantics: semantics.type = semantics

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  given givenDebugSection: DebugSectionSolver.type = DebugSectionSolver

  type Encoded

  def asString(e: Encoded): String

  def abort: Boolean
  def pause: Boolean

  def encodeSymbol(v: Variable): Encoded
  def mkEncoder(bindings: Map[Variable, Encoded])(e: Expr): Encoded
  def mkSubstituter(map: Map[Encoded, Encoded]): Encoded => Encoded

  def mkNot(e: Encoded): Encoded
  def mkOr(es: Encoded*): Encoded
  def mkAnd(es: Encoded*): Encoded
  def mkEquals(l: Encoded, r: Encoded): Encoded
  def mkImplies(l: Encoded, r: Encoded): Encoded

  /** A first-order uninterpreted function of the underlying solver, which an SMT-LIB solver declares
    * with `declare-fun`. Unlike first-class functions, these are never values. */
  type Function

  def mkFunction(name: String, from: Seq[Type], to: Type): Function
  def mkFunApp(f: Function, args: Seq[Encoded]): Encoded

  def extractNot(e: Encoded): Option[Encoded]
  def decodePartial(e: Encoded, tpe: Type): Option[Expr]

  private[unrolling] lazy val trueT = mkEncoder(Map.empty)(BooleanLiteral(true))
  private[unrolling] lazy val falseT = mkEncoder(Map.empty)(BooleanLiteral(false))

  /** The modes of the unfolding that the options select. */
  lazy val modes: UnfoldingModes = new UnfoldingModes(options)

  private var currentGen: Int = 0
  protected def currentGeneration: Int = currentGen
  protected def nextGeneration(gen: Int): Int = gen + 3 + modes.deferFactor

  trait Manager extends IncrementalStateWrapper {
    def unrollGeneration: Option[Int]

    def unroll: Clauses
    def satisfactionAssumptions: Seq[Encoded]
    def refutationAssumptions: Seq[Encoded]
    def promoteBlocker(b: Encoded): Boolean
  }

  /** The pending unfoldings of a manager: the items to unfold under each key (a blocker, or an
    * application whose unfolding a blocker guards), and the generation at which they are unfolded.
    * Items registered under a pending key join it, at the earliest of their generations, and a
    * promoted key is unfolded at the current generation. */
  class UnrollingQueue[K, I] extends IncrementalStateWrapper {
    private val pending = new IncrementalMap[K, (Int, Set[I])]
    protected def extraIncrementals: Seq[IncrementalState] = Seq.empty
    protected val incrementals: Seq[IncrementalState] = pending +: extraIncrementals

    def isEmpty: Boolean = pending.isEmpty
    def contains(key: K): Boolean = pending.contains(key)
    def keys: Iterable[K] = pending.map(_._1)
    def entries: Seq[(K, Int, Set[I])] = pending.toSeq.map { case (k, (gen, items)) => (k, gen, items) }

    /** The earliest generation of the pending keys, if any. */
    def generation: Option[Int] = if (pending.isEmpty) None else Some(pending.values.map(_._1).min)

    def register(key: K, gen: Int, items: Set[I]): Unit = pending.get(key) match {
      case Some((exGen, exItems)) => pending += key -> (gen min exGen, exItems ++ items)
      case None => pending += key -> (gen, items)
    }

    /** Replaces the items of the pending `key`, which keeps its generation. */
    def replace(key: K, items: Set[I]): Unit =
      for ((gen, _) <- pending.get(key)) pending += key -> (gen, items)

    def promote(key: K): Boolean = pending.get(key) match {
      case Some((_, items)) =>
        pending += key -> (currentGeneration, items)
        true
      case None =>
        false
    }

    /** Removes the keys that are due at the current generation, and returns them with their items. */
    def dequeue(): Seq[(K, Int, Set[I])] = {
      val due = pending.toSeq.filter(_._2._1 <= currentGeneration)
      pending --= due.map(_._1)
      due.map { case (k, (gen, items)) => (k, gen, items) }
    }
  }

  /** A queue of the items that blockers guard, whose blockers the model checks assume false. */
  class BlockerQueue[I] extends UnrollingQueue[Encoded, I] {
    // lazy, as the constructor of [[UnrollingQueue]] collects it
    private lazy val negations = new IncrementalMap[Encoded, Encoded]
    override protected def extraIncrementals: Seq[IncrementalState] = Seq(negations)

    override def register(blocker: Encoded, gen: Int, items: Set[I]): Unit = {
      if (!negations.contains(blocker)) negations += blocker -> mkNot(blocker)
      super.register(blocker, gen, items)
    }

    /** The negations of the pending blockers. */
    def satisfactionAssumptions: Seq[Encoded] = keys.toSeq.map(negations)
  }

  private val managers: Seq[Manager] = Seq(
    functionsManager,
    typesManager,
    equalityManager,
    lambdasManager,
    quantificationsManager
  )

  protected def canUnroll: Boolean = managers.exists(_.unrollGeneration.isDefined)
  protected def unroll: Clauses = {
    assert(canUnroll, "Impossible to unroll further")
    currentGen = managers.flatMap(_.unrollGeneration).min + 1
    reporter.debug("Unrolling generation [" + currentGen + "]")
    managers.flatMap(_.unroll)
  }

  protected def satisfactionAssumptions: Seq[Encoded] = managers.flatMap(_.satisfactionAssumptions)
  protected def refutationAssumptions: Seq[Encoded] = managers.flatMap(_.refutationAssumptions)

  // Set of variables that have already been declared in this solver
  private val declared = new IncrementalSet[(Variable, Encoded)]

  val incrementals: Seq[IncrementalState] = managers ++ Seq(witnessState, blockerGraph, partialFunctionState, declared)

  protected def promoteBlocker(b: Encoded, force: Boolean = false): Boolean = {
    var seen: Set[Encoded] = Set.empty
    var promoted: Boolean = false
    var blockers: Seq[Set[Encoded]] = Seq(Set(b))

    // do-while, Scala 3 style
    // See https://docs.scala-lang.org/scala3/reference/dropped-features/do-while.html
    while ({
      val (bs +: rest) = blockers: @unchecked
      blockers = rest

      val allBs = bs ++ bs.flatMap(blockerEquals)
      val next = (for (b <- allBs if !seen(b)) yield {
        seen += b

        for (manager <- managers) {
          val p = manager.promoteBlocker(b)
          promoted = promoted || p
        }

        if (force) {
          blockerChildren(b, strict = false)
        } else {
          Seq.empty[Encoded]
        }
      }).flatten

      if (next.nonEmpty) {
        blockers :+= next
      }
      // The line below is the do-while condition
      !promoted && blockers.nonEmpty}) () // This trailing () is important! If we remove it, it messes with the next statement

    promoted
  }

  type Arg = Either[Encoded, Matcher]

  extension (arg: Arg) {
    def encoded: Encoded = arg match {
      case Left(value) => value
      case Right(matcher) => matcher.encoded
    }

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Arg = arg match {
      case Left(v) => msubst.get(v) match {
        case Some(m) => Right(m)
        case None => Left(substituter(v))
      }
      case Right(m) => Right(m.substitute(substituter, msubst))
    }
  }

  /** The function that a call unfolds: a function of the program, or an uninterpreted function
    * that the model which the solver operates under interprets (see [[interpretation]]). */
  sealed abstract class Callee {
    def signature: String
    def getType: Type
  }

  case class Defined(tfd: TypedFunDef) extends Callee {
    def signature: String = tfd.signature
    def getType: Type = tfd.getType
  }

  /** The uninterpreted function `id` at `tps`, whose calls are the applications of its free function
    * (see [[TemplateGenerator.uninterpretedFunctions]]). */
  case class Interpreted(id: Identifier, tps: Seq[Type]) extends Callee {
    def signature: String = id.asString + tps.map(_.asString).mkString("[", ", ", "]")
    def function: Variable = uninterpretedFunctions(id -> tps)._1
    def getType: Type = function.getType.asInstanceOf[FunctionType].to
  }

  /** An item that a template guards by a blocker: a call, an application, a matcher, a collection
    * read, an equality or a typing. Instantiating the template under the blocker instantiates its
    * items (see [[Instantiation]]). */
  trait Item {
    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Item
  }

  /** Represents a named function call in the unfolding procedure */
  case class Call(callee: Callee, args: Seq[Arg], tpSubst: Seq[Arg]) extends Item {
    override def toString: String = {
      def pArgs(args: Seq[Arg]): String = args.map {
        case Right(m) => m.toString
        case Left(v) => asString(v)
      }.mkString("(", ", ", ")")

      def rec(tpe: Type, args: Seq[Arg]): String = tpe match {
        case ft: FunctionType =>
          val (currArgs, nextArgs) = args.splitAt(ft.from.size)
          pArgs(currArgs) + rec(ft.to, nextArgs)
        case _ => pArgs(args)
      }

      callee.signature + rec(callee.getType, args) + pArgs(tpSubst)
    }

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Call = copy(
      args = args.map(_.substitute(substituter, msubst)),
      tpSubst = tpSubst.map(_.substitute(substituter, msubst))
    )
  }

  /** Represents an application of a first-class function in the unfolding procedure */
  case class App(caller: Encoded, tpe: FunctionType, args: Seq[Arg], encoded: Encoded) extends Item {
    override def toString: String =
      "(" + asString(caller) + " : " + tpe.asString + ")" + args.map(a => asString(a.encoded)).mkString("(", ",", ")")

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): App = copy(
      caller = substituter(caller),
      args = args.map(_.substitute(substituter, msubst)),
      encoded = substituter(encoded)
    )
  }

  /** Represents an E-matching matcher that will be used to instantiate relevant quantified propositions */
  case class Matcher(key: Either[(Encoded, Type), TypedFunDef], args: Seq[Arg], encoded: Encoded) extends Item {
    override def toString: String = (key match {
      case Left((c, tpe)) => asString(c)
      case Right(tfd) => tfd.signature
    }) + args.map {
      case Right(m) => m.toString
      case Left(v) => asString(v)
    }.mkString("(", ",", ")")

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Matcher = copy(
      key = key.left.map(p => substituter(p._1) -> p._2),
      args = args.map(_.substitute(substituter, msubst)),
      encoded = substituter(encoded)
    )
  }

  /** Represents a read of the map, set or bag `collection` of type `tpe` at `key`: a map application,
    * a set membership or a bag multiplicity, or a key that a built collection defines. The value it
    * reads is typed for the free collections that `collection` may equal (@see
    * [[TypeTemplates.Collection]]), as the results of the applications of free functions are. */
  case class Read(tpe: Type, collection: Encoded, key: Encoded) extends Item {
    override def toString: String = asString(collection) + "(" + asString(key) + ")"

    def substitute(substituter: Encoded => Encoded): Read = copy(
      collection = substituter(collection),
      key = substituter(key)
    )

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Read = substitute(substituter)
  }

  /** The keys at which the decompositions of collection types unfold their collection, e.g. `e` in
    * `s == Set(e) ++ rest` (@see [[TemplateGenerator.mkTypeClauses]]). A decomposition types what it
    * unfolds, so the collections it builds at these keys aren't reads. As reads, they would pair
    * the decomposition of each free collection with all the free collections of its type. */
  private[unrolling] val decompositionKeys: MutableSet[Expr] = MutableSet.empty

  /** Represents an equality relation between two instances of a given type */
  case class Equality(tpe: Type, e1: Encoded, e2: Encoded) extends Item {
    override def toString: String =
      s"${asString(e1)} == ${asString(e2)} (of type ${tpe.asString})"

    def substitute(substituter: Encoded => Encoded): Equality = copy(
      e1 = substituter(e1),
      e2 = substituter(e2)
    )

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Equality = substitute(substituter)

    lazy val symbols: (Variable, Encoded) = equalitySymbol(tpe)
  }

  /** Template instantiations
    *
    * [[Template]] instances, when provided with concrete arguments and a
    * blocker, will generate three outputs used for program unfolding:
    * - clauses: clauses that will be added to the underlying solver
    * - call blockers: bookkeeping information necessary for named
    *                  function unfolding
    * - app blockers: bookkeeping information necessary for first-class
    *                 function unfolding
    *
    * This object provides helper methods to deal with the triplets
    * generated during unfolding.
    */

  extension [A,B](map: Map[A,Set[B]]) {
    @annotation.targetName("mergeMapSetMap")
    def merge(that: Map[A,Set[B]]): Map[A,Set[B]] = (map.keys ++ that.keys).map { k =>
      k -> (map.getOrElse(k, Set.empty) ++ that.getOrElse(k, Set.empty))
    }.toMap
    @annotation.targetName("mergeMapSetTuple")
    def merge(that: (A,B)): Map[A,Set[B]] = map + (that._1 -> (map.getOrElse(that._1, Set.empty) + that._2))
  }

  extension [A,B](map: Map[A,Seq[B]]) {
    @annotation.targetName("mergeMapSeqMap")
    def merge(that: Map[A,Seq[B]]): Map[A,Seq[B]] = (map.keys ++ that.keys).map { k =>
      k -> (map.getOrElse(k, Seq.empty) ++ that.getOrElse(k, Seq.empty)).distinct
    }.toMap

    @annotation.targetName("mergeMapSeqTuple")
    def merge(that: (A,B)): Map[A,Seq[B]] = map + (that._1 -> (map.getOrElse(that._1, Seq.empty) :+ that._2))
  }

  /** Abstract templates
    *
    * Pre-compiled sets of clauses with extra bookkeeping information that enables
    * efficient unfolding of function calls and applications.
    * [[Template]] is a super-type for all such clause sets that can be instantiated
    * given a concrete argument list and a blocker in the decision-tree.
    */
  type Clauses    = Seq[Encoded]
  type Apps       = Map[Encoded, Set[App]]
  type Calls      = Map[Encoded, Set[Call]]
  type Types      = Map[Encoded, Set[Typing]]
  type Matchers   = Map[Encoded, Set[Matcher]]
  type Reads = Map[Encoded, Set[Read]]
  type Equalities = Map[Encoded, Set[Equality]]
  type Pointers   = Map[Encoded, Encoded]

  /** The items of a template under their blockers. */
  type Items      = Map[Encoded, Set[Item]]

  extension (items: Items) {
    /** The items that `select` picks, under their blockers. */
    def ofKind[I](select: PartialFunction[Item, I]): Map[Encoded, Set[I]] = items.flatMap { case (b, is) =>
      val selected = is.collect(select)
      if (selected.isEmpty) None else Some(b -> selected)
    }

    def calls: Calls = ofKind { case c: Call => c }
    def apps: Apps = ofKind { case a: App => a }
    def matchers: Matchers = ofKind { case m: Matcher => m }
    def reads: Reads = ofKind { case r: Read => r }
    def equalities: Equalities = ofKind { case e: Equality => e }
    def typings: Types = ofKind { case t: Typing => t }
  }

  /** The items of a map from blockers to items of one kind. */
  def asItems[I <: Item](guarded: Map[Encoded, Set[I]]): Items = guarded.map { case (b, is) => b -> is.toSet[Item] }

  object TemplateContents {
    def empty(pathVar: (Variable, Encoded), args: Seq[(Variable, Encoded)]) =
      TemplateContents(pathVar, args, Map(), Map(), Map(), Seq(), Map(), Seq(), Seq(), Map())
  }

  case class TemplateContents(
    val pathVar   : (Variable, Encoded),
    val arguments : Seq[(Variable, Encoded)],

    val condVars   : Map[Variable, Encoded],
    val exprVars   : Map[Variable, Encoded],
    val condTree   : Map[Variable, Set[Variable]],

    val clauses : Clauses,

    /** The calls, applications, matchers, collection reads, equalities and typings under each blocker. */
    val items   : Items,

    val lambdas         : Seq[LambdaTemplate],
    val quantifications : Seq[QuantificationTemplate],

    val pointers : Pointers,

    /** The failure literals of the body of a function or lambda, which define whether it fails
      * (see [[Instantiation.itemClauses]]), or `None` if the template asserts that they don't hold. */
    val failures : Option[Seq[Encoded]] = None) {

    lazy val args = arguments.map(_._2)

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): TemplateContents =
      TemplateContents(
        pathVar._1 -> substituter(pathVar._2),
        arguments, condVars, exprVars, condTree,
        clauses.map(substituter),
        items.map { case (b, is) => substituter(b) -> is.map(_.substitute(substituter, msubst)) },
        lambdas.map(_.substitute(substituter, msubst)),
        quantifications.map(_.substitute(substituter, msubst)),
        pointers.map(p => substituter(p._1) -> substituter(p._2)),
        failures.map(_.map(substituter))
      )

    /** Instantiates the contents under `aVar`, where the arguments take the values `args`. */
    def instantiation(aVar: Encoded, args: Seq[Arg]): Instantiation =
      instantiation(aVar, (this.args zip args).toMap + (pathVar._2 -> Left(aVar)))

    /** Instantiates the contents under `aVar`, where `baseSubst` gives the values of their symbols. */
    def instantiation(aVar: Encoded, baseSubst: Map[Encoded, Arg]): Instantiation =
      new Instantiation(this, aVar, baseSubst)

    def merge(
      condVars   : Map[Variable, Encoded],
      exprVars   : Map[Variable, Encoded],
      condTree   : Map[Variable, Set[Variable]],
      clauses    : Clauses,
      items      : Items,
      lambdas         : Seq[LambdaTemplate],
      quantifications : Seq[QuantificationTemplate],
      pointers : Pointers
    ): TemplateContents = TemplateContents(
      pathVar,
      arguments,
      this.condVars ++ condVars,
      this.exprVars ++ exprVars,
      this.condTree `merge` condTree,
      this.clauses ++ clauses,
      this.items `merge` items,
      this.lambdas ++ lambdas,
      this.quantifications ++ quantifications,
      this.pointers ++ pointers,
      this.failures
    )
  }

  trait Template { self =>
    val contents: TemplateContents

    lazy val start = contents.pathVar._2

    def instantiate(aVar: Encoded, args: Seq[Arg]): Clauses =
      instantiate(contents.instantiation(aVar, args))

    /** Instantiates the body of a function or lambda, which fails iff `failure` holds. */
    def instantiate(aVar: Encoded, args: Seq[Arg], failure: Encoded): Clauses =
      contents.instantiation(aVar, args).clauses(failure = Some(failure))

    protected def instantiate(instantiation: Instantiation): Clauses = instantiation.clauses()

    override def toString : String = "Instantiated template"
  }

  /** Semi-template used for inner-template equality
    *
    * We introduce a structure here that resembles a [[Template]] that is instantiated
    * ONCE when the corresponding template becomes of interest. */
  class TemplateStructure(

    /** The normalized expression that is shared between all templates that are "equal".
      * Template equality is conditioned on [[body]] equality.
      *
      * @see [[dependencies]] for the other component of equality
      */
    val body: Expr,

    /** The closed expressions (independent of the arguments to [[body]]) contained in
      * the inner-template. Equality is conditionned on equality of [[dependencies]]
      * (inside the solver).
      *
      * @see [[body]] for the other component of equality
      */
    val dependencies: Seq[Encoded],

    val contents: TemplateContents) {

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]) = new TemplateStructure(
      body,
      dependencies.map(substituter),
      contents.substitute(substituter, msubst)
    )

    /** The [[key]] value (triplet of [[body]], a normalization of the `pathVar` of [[contents]] and [[locals]])
      * is used to determine syntactic equality between inner-templates. If the key of two such
      * templates are equal, then they must necessarily be equal in every model.
      *
      * The [[instantiation]] consists of the clause set instantiation (in the sense of
      * [[Instantiation]] that is required for [[dependencies]] to make sense in the solver
      * (introduces blockers, lambdas, quantifications, etc.) Since [[dependencies]] CHANGE during
      * instantiation and [[key]] makes no sense without the associated instantiation, the implicit
      * contract here is that whenever a new key appears during unfolding, its associated
      * instantiation MUST be added to the set of instantiations managed by the solver. However, if
      * an identical (or subsuming) pre-existing key has already been found, then the associated
      * instantiation must already appear in the handled by the solver and the new one can be discarded.
      *
      * The [[locals]] value consists of the [[dependencies]] on which the substitution resulting
      * from instantiation has been applied. The [[dependencies]] should not be directly used here
      * as they may depend on closure and quantifier ids that were only obtained when [[instantiation]]
      * was computed.
      *
      * The [[instantiationSubst]] substitution corresponds that applied to [[dependencies]] when
      * constructing [[locals]].
      */
    lazy val (key, instantiation, locals, instantiationSubst) = {
      val inst = contents.instantiation(contents.pathVar._2, Map.empty[Encoded, Arg])
      val instantiation = inst.clauses()
      val substMap = inst.substMap

      val deps = dependencies.map(inst.substituter)
      val key = (body, blockerPath(contents.pathVar._2), deps)

      val sortedDeps = exprOps.variablesOf(body).toSeq.sortBy(_.id)
      val locals = sortedDeps zip deps
      (key, instantiation, locals, substMap.view.mapValues(_.encoded).toMap)
    }

    override def equals(that: Any): Boolean = that match {
      case (struct: TemplateStructure) => key == struct.key
      case _ => false
    }

    override def hashCode: Int = key.hashCode

    def subsumes(that: TemplateStructure): Boolean = {
      key._1 == that.key._1 && key._3 == that.key._3 && key._2.subsetOf(that.key._2)
    }
  }

  object Template {

    private def collectSelectors(expr: Expr, ptr: Expr): Seq[(Expr, Variable)] = expr match {
      case adt @ ADT(id, tps, es) => (adt.getConstructor.fields zip es).flatMap {
        case (vd, e) => collectSelectors(e, ADTSelector(ptr, vd.id))
      }

      case Tuple(es) => es.zipWithIndex.flatMap {
        case (e, i) => collectSelectors(e, TupleSelect(ptr, i + 1))
      }

      case IsTyped(v: Variable, _: FunctionType) => Seq(ptr -> v)
      case _ => Seq.empty
    }

    private def resultPointers(encoder: Expr => Encoded)(expr: Expr): Map[Encoded, Encoded] = {
      val pointers = expr match {
        case Equals(v @ (_: Variable | _: FunctionInvocation | _: Application), e) => collectSelectors(e, v).toMap
        case Equals(e, v @ (_: Variable | _: FunctionInvocation | _: Application)) => collectSelectors(e, v).toMap
        case _ => Map.empty[Expr, Variable]
      }

      pointers.map(p => encoder(p._1) -> encoder(p._2))
    }

    def lambdaPointers(encoder: Expr => Encoded)(expr: Expr): Map[Encoded, Encoded] = {

      val pointers = exprOps.collect {
        case FunctionInvocation(_, _, es) => es.flatMap(e => collectSelectors(e, e)).toSet
        case Application(_, es) => es.flatMap(e => collectSelectors(e, e)).toSet
        case e: Tuple => collectSelectors(e, e).toSet
        case e: ADT => collectSelectors(e, e).toSet
        case _ => Set.empty[(Expr, Variable)]
      } (expr).toMap

      pointers.map(p => encoder(p._1) -> encoder(p._2))
    }

    /** The calls, applications, matchers and collection reads of an expression, and its lambda pointers. */
    case class ExtractedCalls(items: Set[Item], pointers: Pointers)

    /** The encoding of [[TemplateClauses]]: the encoded clauses and the items under each blocker,
      * i.e. the calls, applications, matchers and collection reads of the clauses, and their
      * equalities and typings (see [[encode]]). */
    case class Encoding(clauses: Clauses, items: Items, pointers: Pointers, stringRepr: () => String)

    def extractCalls(
      expr: Expr,
      substMap: Map[Variable, Encoded] = Map.empty[Variable, Encoded],
      optCall: Option[(Callee, Seq[Arg])] = None,
      optApp: Option[App] = None
    ): ExtractedCalls = {
      val encoder : Expr => Encoded = mkEncoder(substMap)

      val pointers = lambdaPointers(encoder)(expr)

      val exprToMatcher = exprOps.fold[Map[Expr, Matcher]] { (expr, res) =>
        val result = res.flatten.toMap

        result ++ (expr match {
          case QuantificationMatcher(c, Seq(e1, _)) if c == equalitySymbol(e1.getType)._1 => None
          case QuantificationMatcher(c, args) =>
            // Note that we rely here on the fact that foldRight visits the matcher's arguments first,
            // so any Matcher in arguments will belong to the `result` map
            val encodedArgs = args.map(arg => result.get(arg) match {
              case Some(matcher) => Right(matcher)
              case None => Left(encoder(arg))
            })

            Some(expr -> Matcher(Left(encoder(c) -> c.getType), encodedArgs, encoder(expr)))
          case FunctionMatcher(tfd, args) =>
            // see comment above
            val encodedArgs = args.map(arg => result.get(arg) match {
              case Some(matcher) => Right(matcher)
              case None => Left(encoder(arg))
            })

            Some(expr -> Matcher(Right(tfd), encodedArgs, encoder(expr)))
          case _ => None
        })
      }(expr)

      def encodeArg(arg: Expr): Arg = exprToMatcher.get(arg) match {
        case Some(matcher) => Right(matcher)
        case None => Left(encoder(arg))
      }

      val calls = exprOps.collect[Call] {
        case FunctionInvocation(id, tps, args) =>
          val tpVars = tps.flatMap(variableSeq).distinct
          Set(Call(Defined(getFunction(id, tps)), args.map(encodeArg), tpVars.map(encodeArg)))
        // The applications of the free functions of interpreted uninterpreted functions unfold their
        // interpretations
        case Application(f: Variable, args) => interpretedFunctions.get(f) match {
          case Some(callee) => Set(Call(callee, args.map(encodeArg), Seq.empty))
          case None => Set.empty
        }
        case _ => Set.empty
      } (expr).filter { case Call(callee, args, _) =>
        !optCall.exists(p => p._1 == callee && p._2 == args)
      }

      val apps = exprOps.collect[Application] {
        case app: Application => Set(app)
        case _ => Set.empty
      } (expr).filter {
        case Application(c, Seq(e1, e2)) => c != equalitySymbol(e1.getType)._1
        case _ => true
      }.map { case app @ Application(c, args) =>
        val tpe = c.getType.asInstanceOf[FunctionType]
        App(encoder(c), tpe, args.map(encodeArg), encoder(app))
      }.filter(i => Some(i) != optApp)

      val matchers = exprToMatcher.values.toSet
        .filter(i => Some(i.encoded) != optApp.map(_.encoded))
        .filter {
          case Matcher(Right(tfd), args, _) => !optCall.exists(p => p._1 == Defined(tfd) && p._2 == args)
          case _ => true
        }

      // The keys that a built collection defines: the elements of a finite set or bag, the keys of
      // a finite or updated map, and the keys that the collections it is built from define
      def definedKeys(e: Expr): Seq[Expr] = e match {
        case FiniteMap(pairs, _, _, _) => pairs.map(_._1)
        case MapUpdated(m, k, _) => k +: definedKeys(m)
        case FiniteSet(elems, _) => elems
        case SetAdd(s, e) => e +: definedKeys(s)
        case SetUnion(s1, s2) => definedKeys(s1) ++ definedKeys(s2)
        case SetIntersection(s1, s2) => definedKeys(s1) ++ definedKeys(s2)
        case SetDifference(s1, _) => definedKeys(s1)
        case FiniteBag(pairs, _) => pairs.map(_._1)
        case BagAdd(b, e) => e +: definedKeys(b)
        case BagUnion(b1, b2) => definedKeys(b1) ++ definedKeys(b2)
        case BagIntersection(b1, b2) => definedKeys(b1) ++ definedKeys(b2)
        case BagDifference(b1, _) => definedKeys(b1)
        case _ => Seq.empty
      }

      // A collection is read where the formula looks it up, and where it is built at the keys it
      // defines, so that a free collection that equals a built one types these keys. The collections
      // that type decompositions build are left out (see [[decompositionKeys]]).
      val reads = exprOps.collect[Read] {
        case MapApply(m, k) => Set(Read(m.getType, encoder(m), encoder(k)))
        case ElementOfSet(e, s) => Set(Read(s.getType, encoder(s), encoder(e)))
        case MultiplicityInBag(e, b) => Set(Read(b.getType, encoder(b), encoder(e)))
        case c @ (_: FiniteMap | _: MapUpdated | _: FiniteSet | _: SetAdd | _: SetUnion | _: SetIntersection |
                  _: SetDifference | _: FiniteBag | _: BagAdd | _: BagUnion | _: BagIntersection | _: BagDifference) =>
          definedKeys(c).filterNot(decompositionKeys).map(k => Read(c.getType, encoder(c), encoder(k))).toSet
        case _ => Set.empty
      } (expr)

      ExtractedCalls(calls.toSet[Item] ++ apps ++ matchers ++ reads, pointers)
    }

    /** The failure literals among the expression variables of a template (see [[failureSymbols]]). */
    def failures(exprVars: Map[Variable, Encoded]): Seq[Encoded] =
      exprVars.toSeq.collect { case (v, vT) if failureSymbols(v) => vT }

    def encode(
      pathVar: (Variable, Encoded),
      arguments: Seq[(Variable, Encoded)],
      tmplClauses: TemplateClauses,
      substMap: Map[Variable, Encoded] = Map.empty[Variable, Encoded],
      optCall: Option[Callee] = None,
      optApp: Option[(Encoded, FunctionType)] = None,
      partial: Boolean = false
    ): Encoding = {
      import tmplClauses.{condVars, exprVars, guardedExprs, equations => eqs, lambdas, quantifications => quants}
      val equals = tmplClauses.equalities

      val idToTrId : Map[Variable, Encoded] =
        condVars ++ exprVars + pathVar ++ arguments ++ substMap ++
        lambdas.map(_.ids) ++ quants.flatMap(_.mapping) ++ equals.flatMap(_._2.map(_.symbols)) ++
        typesManager.tpSubst ++ uninterpretedSubst
      val encoder: Expr => Encoded = mkEncoder(idToTrId)

      val optIdCall = optCall.map { callee => (callee, arguments.map(p => Left(p._2))) }
      val optIdApp = optApp.map { case (idT, tpe) =>
        App(idT, tpe, arguments.map(p => Left(p._2)), mkApp(idT, tpe, arguments.map(_._2)))
      }

      val (clauses, items, pointers) = {
        var clauses  : Clauses  = Seq.empty
        var items    : Items    = asItems(tmplClauses.types) `merge` asItems(equals)
        var pointers : Pointers = Map.empty

        val pv = pathVar._1
        for ((b,es) <- guardedExprs `merge` Map(pv -> eqs)) {
          var bItems : Set[Item] = Set.empty
          for (e <- es) {
            val extracted = extractCalls(e, idToTrId, optIdCall, optIdApp)
            bItems ++= extracted.items
            pointers ++= extracted.pointers
          }

          if (bItems.nonEmpty) items = items `merge` Map(idToTrId(b) -> bItems)
        }

        for (e <- guardedExprs.getOrElse(pv, Seq.empty)) {
          pointers ++= resultPointers(encoder)(e)
        }

        clauses ++= (for ((b,es) <- guardedExprs; e <- es) yield encoder(Implies(b, e)))
        clauses ++= eqs.map(encoder)

        // The failure literals of the body of a function or lambda define whether it fails (see
        // [[Instantiation.itemClauses]]), while other templates assert that they don't hold
        if (!partial) clauses ++= failures(exprVars).map(mkNot)

        (clauses, items, pointers)
      }

      val stringRepr : () => String = () => {
        val (blockers, applications, matchers, reads) = (items.calls, items.apps, items.matchers, items.reads)
        " * Activating boolean : " + pathVar._1.asString + "\n" +
        " * Control booleans   : " + condVars.keys.map(_.asString).mkString(", ") + "\n" +
        " * Expression vars    : " + exprVars.keys.map(_.asString).mkString(", ") + "\n" +
        " * Clauses            : " + (if (guardedExprs.isEmpty) "\n" else {
          "\n   " + (for ((b,es) <- guardedExprs; e <- es) yield (b.asString + " ==> " + e.asString)).mkString("\n   ") + "\n"
        }) +
        " * Invocation-blocks  :" + (if (blockers.isEmpty) "\n" else {
          "\n   " + blockers.map(p => asString(p._1) + " ==> " + p._2).mkString("\n   ") + "\n"
        }) +
        " * Application-blocks :" + (if (applications.isEmpty) "\n" else {
          "\n   " + applications.map(p => asString(p._1) + " ==> " + p._2).mkString("\n   ") + "\n"
        }) +
        " * Matchers           :" + (if (matchers.isEmpty) "\n" else {
          "\n   " + matchers.map(p => asString(p._1) + " ==> " + p._2).mkString("\n   ") + "\n"
        }) +
        " * Collection reads   :" + (if (reads.isEmpty) "\n" else {
          "\n   " + reads.map(p => asString(p._1) + " ==> " + p._2).mkString("\n   ") + "\n"
        }) +
        " * Lambdas            :\n" + lambdas.map { case template =>
          " +> " + template.toString.split("\n").mkString("\n    ") + "\n"
        }.mkString("\n") +
        " * Foralls            :\n" + quants.map { case template =>
          " +> " + template.toString.split("\n").mkString("\n    ") + "\n"
        }.mkString("\n")
      }

      Encoding(clauses, items, pointers, stringRepr)
    }

    def contents(
      pathVar: (Variable, Encoded),
      arguments: Seq[(Variable, Encoded)],
      tmplClauses: TemplateClauses,
      substMap: Map[Variable, Encoded] = Map.empty,
      optCall: Option[Callee] = None,
      optApp: Option[(Encoded, FunctionType)] = None,
      partial: Boolean = false
    ): (TemplateContents, () => String) = {

      val encoding = Template.encode(
        pathVar, arguments, tmplClauses, substMap = substMap, optCall = optCall, optApp = optApp, partial = partial)

      val contents = TemplateContents(
        pathVar, arguments, tmplClauses.condVars, tmplClauses.exprVars, tmplClauses.condTree,
        encoding.clauses, encoding.items, tmplClauses.lambdas, tmplClauses.quantifications, encoding.pointers,
        if (partial) Some(failures(tmplClauses.exprVars)) else None
      )

      (contents, encoding.stringRepr)
    }

  }

  /** The instantiation of the contents of a template under the blocker `aVar`, where `baseSubst`
    * gives the values of the arguments (and of the start blocker of the contents).
    *
    * Instantiation proceeds in two stages. Creating an [[Instantiation]] runs the substitution
    * stage, which builds [[substMap]] by
    *  1. giving fresh symbols to the expression and condition variables,
    *  2. instantiating the typings, which registers functions before the matchers of the
    *     quantifications are instantiated,
    *  3. instantiating the lambdas, in the order of their dependencies,
    *  4. instantiating the quantifications, the positive ones last, and
    *  5. registering the lambda pointers.
    *
    * [[clauses]] then runs the item stage, which instantiates
    *  6. the calls and applications, which define whether the template fails, and then
    *  7. the matchers, collection reads and equalities.
    */
  final class Instantiation private[unrolling] (
    contents: TemplateContents,
    aVar: Encoded,
    baseSubst: Map[Encoded, Arg]
  ) {
    private val matcherSubst = baseSubst.collect { case (c, Right(m)) => c -> m }
    private var subst: Map[Encoded, Arg] = baseSubst
    private val buffer = new scala.collection.mutable.ListBuffer[Encoded]

    private def substitution: Map[Encoded, Encoded] = subst.view.mapValues(_.encoded).toMap

    private def freshSymbols(): Unit = {
      val freshSubst = contents.exprVars.map { case (v, vT) => vT -> encodeSymbol(v) } ++
                       freshConds(aVar, contents.condVars, contents.condTree)
      subst = freshSubst.view.mapValues(Left(_)).toMap ++ baseSubst
    }

    // We instantiate types before quantifications in order to register functions
    // before trying to instantiate matchers introduced by quantifications
    private def typings(): Unit = {
      val substituter = mkSubstituter(substitution)
      for ((b, tps) <- contents.items.typings if !abort; bp = substituter(b); tp <- tps if !abort) {
        buffer ++= instantiateType(bp, tp.substitute(substituter, matcherSubst))
      }
    }

    // /!\ CAREFUL /!\
    // We have to be wary while computing the lambda subst map since lambdas can
    // depend on each other. However, these dependencies cannot be cyclic so it
    // suffices to make sure the traversal order is correct.
    private def lambdas(): Unit = {
      var seen : Set[LambdaTemplate] = Set.empty

      val lambdaKeys = contents.lambdas.map(lambda => lambda.ids._2 -> lambda).toMap
      def extractSubst(lambda: LambdaTemplate): Unit = {
        for {
          dep <- lambda.closures.map(_._2) flatMap lambdaKeys.get
          if !seen(dep)
        } extractSubst(dep)

        if (!seen(lambda)) {
          val substLambda = lambda.substitute(mkSubstituter(substitution), matcherSubst)
          val (idT, cls) = instantiateLambda(substLambda)
          subst += lambda.ids._2 -> Left(idT)
          buffer ++= cls
          seen += lambda
        }
      }

      for (l <- contents.lambdas) extractSubst(l)
    }

    // instantiate positive quantifications last to avoid introducing
    // extra quantifier instantiations that arise due to empty domains
    private def quantifications(): Unit = {
      val (others, positives) = contents.quantifications.partition(_.polarity.isNegative)
      for (q <- others ++ positives) {
        val substQuant = q.substitute(mkSubstituter(substitution), matcherSubst)
        val (map, cls) = instantiateQuantification(substQuant)
        subst ++= map.view.mapValues(Left(_)).toMap
        buffer ++= cls
      }
    }

    private def pointers(): Unit = {
      val substituter = mkSubstituter(substitution)
      for ((ptr, lambda) <- contents.pointers) {
        registerLambda(substituter(ptr), substituter(lambda))
      }
    }

    freshSymbols()
    typings()
    lambdas()
    quantifications()
    pointers()

    /** The clauses of the substitution stage. */
    val substClauses: Clauses = buffer.toSeq

    /** The values of the symbols of the contents. */
    val substMap: Map[Encoded, Arg] = subst

    lazy val substituter: Encoded => Encoded = mkSubstituter(substitution)
    lazy val msubst: Map[Encoded, Matcher] = substMap.collect { case (c, Right(m)) => c -> m }

    /** The clauses of both stages (see [[itemClauses]]). */
    def clauses(
      failure: Option[Encoded] = None,
      exempt: App => Boolean = _ => false,
      onMatcher: (Encoded, Matcher) => Clauses = instantiateMatcher(_, _),
      onEquality: (Encoded, Equality) => Clauses = instantiateEquality(_, _)
    ): Clauses = substClauses ++ itemClauses(failure, exempt, onMatcher, onEquality)

    /** Instantiates the clauses and the items of the contents under their blockers: first the calls
      * and applications, then the matchers, collection reads and equalities.
      *
      * The body of a function or lambda fails iff `failure` holds, while other templates assert
      * that their failure literals don't hold. The applications that `exempt` picks may fail. The
      * templates that handle matchers or equalities differently pass `onMatcher` or `onEquality`,
      * which receive these items under their substituted blockers. */
    def itemClauses(
      failure: Option[Encoded] = None,
      exempt: App => Boolean = _ => false,
      onMatcher: (Encoded, Matcher) => Clauses = instantiateMatcher(_, _),
      onEquality: (Encoded, Equality) => Clauses = instantiateEquality(_, _)
    ): Clauses = {
      val literals = contents.failures.getOrElse(Seq.empty)

      val allClauses = new scala.collection.mutable.ListBuffer[Encoded]
      if (failure.isEmpty) allClauses ++= literals.map(f => mkNot(substituter(f)))
      allClauses ++= contents.clauses.map(substituter)

      // Applies `f` to the items that `select` picks, under their substituted blockers
      def each[I](select: PartialFunction[Item, I])(f: (Encoded, I) => Unit): Unit =
        for ((b, is) <- contents.items if !abort; bp = substituter(b); i <- is.collect(select) if !abort) f(bp, i)

      // The calls and applications that may fail, under their blockers
      val failing = new scala.collection.mutable.ListBuffer[Encoded]
      def mayFail(b: Encoded, fails: => Encoded): Unit = if (modes.partialFunctions) {
        if (failure.isDefined) failing += mkAnd(b, fails) else allClauses += mkImplies(b, mkNot(fails))
      }

      each { case c: Call => c } { (bp, fi) =>
        val call = fi.substitute(substituter, msubst)
        mayFail(bp, callFailure(call))
        allClauses ++= instantiateCall(bp, call)
      }

      each { case a: App => a } { (bp, fa) =>
        val app = fa.substitute(substituter, msubst)
        if (!exempt(app)) mayFail(bp, appFailure(app))
        allClauses ++= instantiateApp(bp, app)
      }

      // The body of a function or lambda fails iff one of its failure literals holds, or one of the
      // calls and applications on its paths fails
      for (self <- failure if modes.partialFunctions) {
        val sources = literals.map(substituter) ++ failing
        val fails = sources match {
          case Seq() => falseT
          case Seq(source) => source
          case _ => mkOr(sources.toSeq*)
        }
        allClauses += mkImplies(substituter(contents.pathVar._2), mkEquals(self, fails))
      }
      allClauses ++= newFailureDefinitions()

      each { case m: Matcher => m } { (bp, m) =>
        allClauses ++= onMatcher(bp, m.substitute(substituter, msubst))
      }

      each { case r: Read => r } { (bp, r) =>
        allClauses ++= instantiateRead(bp, r.substitute(substituter))
      }

      each { case e: Equality => e } { (bp, e) =>
        allClauses ++= onEquality(bp, e.substitute(substituter))
      }

      allClauses.toSeq
    }
  }

  private def instantiate(
    bindings: Map[Variable, Encoded],
    gen: (Variable, Encoded) => TemplateClauses,
    exempt: App => Boolean = _ => false
  ): Clauses = {
    val start = Variable.fresh("start", BooleanType(), true)
    val encodedStart = encodeSymbol(start)

    val tmplClauses = gen(start, encodedStart)

    val (contents, _) = Template.contents(start -> encodedStart, bindings.toSeq, tmplClauses)
    val allClauses = encodedStart +:
      contents.instantiation(encodedStart, Map.empty[Encoded, Arg]).clauses(exempt = exempt)

    for (cl <- allClauses) {
      reporter.debug("  . " + cl)
    }

    allClauses
  }

  protected def instantiateVariable(v: Variable, bindings: Map[Variable, Encoded]): Clauses = {
    if (declared `contains` (v -> bindings(v))) {
      Seq.empty
    } else {
      declared += v -> bindings(v)
      instantiate(bindings, { (start, encodedStart) =>
        mkClauses1(start, v.tpe, v, bindings + (start -> encodedStart))(using FreeGenerator)
      })
    }
  }

  /** Instantiates a distinguishing input for the first-class functions `f1` and `f2` of type `tpe`.
    *
    * Fresh witness arguments `ws` are introduced such that `f1` and `f2` differ on `ws` whenever
    * `guard` holds and `f1 != f2`: one of `f1(ws)` and `f2(ws)` fails and the other doesn't, or
    * neither fails and `f1(ws) != f2(ws)`. The applications on `ws` are the only ones whose failure
    * the witness doesn't exclude. The witnesses are typed as free variables, so function-typed
    * witnesses are themselves registered as free functions (and will in turn receive witnesses).
    *
    * @see [[LambdaTemplates]] for a discussion of how these witnesses are used.
    */
  def instantiateWitness(guard: Encoded, tpe: FunctionType, f1: Encoded, f2: Encoded): Clauses = {
    val v1 = Variable.fresh("f", tpe, true)
    val v2 = Variable.fresh("g", tpe, true)
    val ws = tpe.from.map(tp => Variable.fresh("w", tp, true))
    val bindings = Map(v1 -> f1, v2 -> f2) ++ ws.map(w => w -> encodeSymbol(w))
    recordDistinguishingInput(f1, f2, tpe, ws.map(bindings))

    // the compared functions have already been typed where they were registered
    declared += v1 -> f1
    declared += v2 -> f2

    // whether the results of the applications on `ws` differ
    val differ = Variable.fresh("differ", BooleanType(), true)
    val differT = encodeSymbol(differ)
    val wsT = ws.map(bindings)
    // Only extensional equality observes where functions fail (see [[UnfoldingModes.partialFunctions]]). Without
    // function equality, distinguishing inputs only tell apart the functions of models, whose tests
    // can't observe failures (applying a function where it fails fails the test).
    val partial = modes.partialFunctions
    def isWitnessApp(app: App): Boolean = partial &&
      (app.caller == f1 || app.caller == f2) && app.tpe == tpe && app.args.map(_.encoded) == wsT

    val clauses = instantiate(bindings + (differ -> differT), { (start, encodedStart) =>
      val substMap = bindings + (differ -> differT) + (start -> encodedStart)
      val tmplClauses = mkClauses0(start,
        Equals(differ, Not(Equals(Application(v1, ws), Application(v2, ws)))), substMap)
      val tpeClauses = ws.map { w =>
        declared += w -> bindings(w)
        mkClauses1(start, w.tpe, w, substMap)(using FreeGenerator)
      }

      tpeClauses.foldLeft(tmplClauses)(_ ++ _)
    }, isWitnessApp)

    // `instantiate` asserts the start blocker, which we replace with the witness condition
    val encodedStart +: rest = clauses: @unchecked
    val (err1, err2) = (appFailure(f1, tpe, wsT), appFailure(f2, tpe, wsT))
    val distinguished = if (!partial) differT else mkOr(mkNot(mkEquals(err1, err2)), mkAnd(mkNot(err1), mkNot(err2), differT))
    (mkEquals(encodedStart, mkAnd(guard, mkNot(mkEquals(f1, f2)))) +: mkImplies(encodedStart, distinguished) +: rest) ++
      newFailureDefinitions()
  }

  protected def instantiateExpr(expr: Expr, bindings: Map[Variable, Encoded]): Clauses = {
    instantiate(bindings, { (start, encodedStart) =>
      val instExpr = timers.solvers.simplify.run { simplifyFormula(expr) }

      val tmplClauses = mkClauses0(start, instExpr, bindings + (start -> encodedStart), polarity = Some(true))
      val tpeClauses = bindings.filterNot(declared `contains` _).map { case (v, s) =>
        declared += v -> s
        mkClauses1(start, v.tpe, v, bindings + (start -> encodedStart))(using FreeGenerator)
      }

      tpeClauses.foldLeft(tmplClauses)(_ ++ _)
    })
  }
}
