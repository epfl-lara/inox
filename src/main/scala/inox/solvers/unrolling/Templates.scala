/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.generic.CanBuildFrom

trait Templates
  extends TemplateGenerator
     with FunctionTemplates
     with DatatypeTemplates
     with EqualityTemplates
     with LambdaTemplates
     with QuantificationTemplates
     with IncrementalStateWrapper {

  val program: Program
  val context: Context

  import context._
  import program._
  import program.trees._
  import program.symbols._

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

  def extractNot(e: Encoded): Option[Encoded]

  private[unrolling] lazy val trueT = mkEncoder(Map.empty)(BooleanLiteral(true))
  private[unrolling] lazy val falseT = mkEncoder(Map.empty)(BooleanLiteral(false))

  protected lazy val deferFactor =  3 * options.findOptionOrDefault(optModelFinding)

  private var currentGen: Int = 0
  protected def currentGeneration: Int = currentGen
  protected def nextGeneration(gen: Int): Int = gen + 3 + deferFactor

  trait Manager extends IncrementalStateWrapper {
    def unrollGeneration: Option[Int]

    def unroll: Clauses
    def satisfactionAssumptions: Seq[Encoded]
    def refutationAssumptions: Seq[Encoded]
    def promoteBlocker(b: Encoded): Boolean
  }

  private val managers: Seq[Manager] = Seq(
    functionsManager,
    datatypesManager,
    equalityManager,
    lambdasManager,
    quantificationsManager
  )

  def canUnroll: Boolean = managers.exists(_.unrollGeneration.isDefined)
  def unroll: Clauses = {
    assert(canUnroll, "Impossible to unroll further")
    currentGen = managers.flatMap(_.unrollGeneration).min + 1
    reporter.debug("Unrolling generation [" + currentGen + "]")
    managers.flatMap(_.unroll)
  }

  def satisfactionAssumptions = managers.flatMap(_.satisfactionAssumptions)
  def refutationAssumptions = managers.flatMap(_.refutationAssumptions)

  // implication tree that we're sure about: if  (b1, b2) is in the tree, then
  // we have the precise semantics of b1 ==> b2 in the resulting clause set
  private val condImplies = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)
  private val condImplied = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)

  // implication tree that isn't quite ensured in the resulting clause set
  // this can happen due to defBlocker caching in unrolling
  private val potImplies = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)
  private val potImplied = new IncrementalMap[Encoded, Set[Encoded]].withDefaultValue(Set.empty)

  private val condEquals  = new IncrementalBijection[Encoded, Set[Encoded]]

  val incrementals: Seq[IncrementalState] = managers ++ Seq(
    condImplies, condImplied, potImplies, potImplied, condEquals
  )

  protected def freshConds(
    pathVar: Encoded,
    condVars: Map[Variable, Encoded],
    tree: Map[Variable, Set[Variable]]): Map[Encoded, Encoded] = {

    val subst = condVars.map { case (v, idT) => idT -> encodeSymbol(v) }
    val mapping = condVars.mapValues(subst)

    for ((parent, children) <- tree) {
      mapping.get(parent) match {
        case None => // enabling condition, corresponds to pathVar
          for (child <- children) {
            val ec = mapping(child)
            condImplies += pathVar -> (condImplies(pathVar) + ec)
            condImplied += ec -> (condImplied(ec) + pathVar)
          }

        case Some(ep) =>
          for (child <- children) {
            val ec = mapping(child)
            condImplies += ep -> (condImplies(ep) + ec)
            condImplied += ec -> (condImplied(ec) + ep)
          }
      }
    }

    subst
  }

  private val sym = Variable.fresh("bs", BooleanType, true)
  protected def encodeBlockers(bs: Set[Encoded]): (Encoded, Clauses) = bs.toSeq match {
    case Seq(b) if (
      condImplies.isDefinedAt(b) || condImplied.isDefinedAt(b) ||
      potImplies.isDefinedAt(b) || potImplied.isDefinedAt(b) ||
      condEquals.containsA(b)
    ) => (b, Seq.empty)

    case _ =>
      val flatBs = fixpoint((bs: Set[Encoded]) => bs.flatMap(b => condEquals.getBorElse(b, Set(b))))(bs)
      condEquals.getA(flatBs) match {
        case Some(b) => (b, Seq.empty)
        case None =>
          val b = encodeSymbol(sym)
          condEquals += (b -> flatBs)
          (b, Seq(mkEquals(b, if (flatBs.isEmpty) trueT else mkAnd(flatBs.toSeq : _*))))
      }
  }

  protected def registerImplication(b1: Encoded, b2: Encoded): Unit = {
    potImplies += b1 -> (potImplies(b1) + b2)
    potImplied += b2 -> (potImplied(b2) + b1)
  }

  protected def blockerEquals(b: Encoded): Set[Encoded] = condEquals.getBorElse(b, Set.empty)

  protected def blockerParents(b: Encoded, strict: Boolean = true): Set[Encoded] = {
    condImplied(b) ++ (if (!strict) potImplied(b) else Set.empty)
  }

  protected def blockerChildren(b: Encoded, strict: Boolean = true): Set[Encoded] = {
    condImplies(b) ++ (if (!strict) potImplies(b) else Set.empty)
  }

  protected def blockerPath(b: Encoded): Set[Encoded] = blockerPath(Set(b))

  /* This set is guaranteed finite and won't expand beyond the limit of a function's
   * definition as aVar ==> defBlocker is NOT a strict implication (ie. won't be in
   * the condImplied map) */
  protected def blockerPath(bs: Set[Encoded]): Set[Encoded] = fixpoint((bs: Set[Encoded]) => bs.flatMap { b =>
    val equal = condEquals.getBorElse(b, Set.empty)
    if (equal.nonEmpty) equal else (condImplied(b) + b)
  })(bs)

  def promoteBlocker(b: Encoded, force: Boolean = false): Boolean = {
    var seen: Set[Encoded] = Set.empty
    var promoted: Boolean = false
    var blockers: Seq[Set[Encoded]] = Seq(Set(b))

    do {
      val (bs +: rest) = blockers
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

      if (next.nonEmpty) blockers :+= next
    } while (!promoted && blockers.nonEmpty)

    promoted
  }

  implicit val debugSection = DebugSectionSolver

  type Arg = Either[Encoded, Matcher]

  implicit class ArgWrapper(arg: Arg) {
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

  /** Represents a named function call in the unfolding procedure */
  case class Call(tfd: TypedFunDef, args: Seq[Arg]) {
    override def toString = tfd.signature + {
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

      rec(tfd.returnType, args)
    }

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Call = copy(
      args = args.map(_.substitute(substituter, msubst))
    )
  }

  /** Represents an application of a first-class function in the unfolding procedure */
  case class App(caller: Encoded, tpe: FunctionType, args: Seq[Arg], encoded: Encoded) {
    override def toString: String =
      "(" + asString(caller) + " : " + tpe.asString + ")" + args.map(a => asString(a.encoded)).mkString("(", ",", ")")

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): App = copy(
      caller = substituter(caller),
      args = args.map(_.substitute(substituter, msubst)),
      encoded = substituter(encoded)
    )
  }

  /** Represents an E-matching matcher that will be used to instantiate relevant quantified propositions */
  case class Matcher(key: Either[(Encoded, Type), TypedFunDef], args: Seq[Arg], encoded: Encoded) {
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

  /** Represents an equality relation between two instances of a given type */
  case class Equality(tpe: Type, e1: Encoded, e2: Encoded) {
    override def toString: String =
      s"${asString(e1)} == ${asString(e2)} (of type ${tpe.asString})"

    def substitute(substituter: Encoded => Encoded): Equality = copy(
      e1 = substituter(e1),
      e2 = substituter(e2)
    )

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
  type Clauses       = Seq[Encoded]
  type CallBlockers  = Map[Encoded, Set[Call]]
  type TypeBlockers  = Map[Encoded, Set[TemplateTypeInfo]]
  type AppBlockers   = Map[(Encoded, App), Set[TemplateAppInfo]]

  implicit class MapSetWrapper[A,B](map: Map[A,Set[B]]) {
    def merge(that: Map[A,Set[B]]): Map[A,Set[B]] = (map.keys ++ that.keys).map { k =>
      k -> (map.getOrElse(k, Set.empty) ++ that.getOrElse(k, Set.empty))
    }.toMap

    def merge(that: (A,B)): Map[A,Set[B]] = map + (that._1 -> (map.getOrElse(that._1, Set.empty) + that._2))
  }

  implicit class MapSeqWrapper[A,B](map: Map[A,Seq[B]]) {
    def merge(that: Map[A,Seq[B]]): Map[A,Seq[B]] = (map.keys ++ that.keys).map { k =>
      k -> (map.getOrElse(k, Seq.empty) ++ that.getOrElse(k, Seq.empty)).distinct
    }.toMap

    def merge(that: (A,B)): Map[A,Seq[B]] = map + (that._1 -> (map.getOrElse(that._1, Seq.empty) :+ that._2))
  }

  /** Abstract templates
    *
    * Pre-compiled sets of clauses with extra bookkeeping information that enables
    * efficient unfolding of function calls and applications.
    * [[Template]] is a super-type for all such clause sets that can be instantiated
    * given a concrete argument list and a blocker in the decision-tree.
    */
  type Apps       = Map[Encoded, Set[App]]
  type Calls      = Map[Encoded, Set[Call]]
  type Matchers   = Map[Encoded, Set[Matcher]]
  type Equalities = Map[Encoded, Set[Equality]]
  type Pointers   = Map[Encoded, Encoded]

  object TemplateContents {
    def empty(pathVar: (Variable, Encoded), args: Seq[(Variable, Encoded)]) =
      TemplateContents(pathVar, args, Map(), Map(), Map(), Map(), Seq(), Map(), Map(), Map(), Map(), Seq(), Seq(), Map())
  }

  case class TemplateContents(
    val pathVar   : (Variable, Encoded),
    val arguments : Seq[(Variable, Encoded)],

    val condVars   : Map[Variable, Encoded],
    val exprVars   : Map[Variable, Encoded],
    val chooseVars : Map[Variable, Encoded],
    val condTree   : Map[Variable, Set[Variable]],

    val clauses      : Clauses,
    val blockers     : Calls,
    val applications : Apps,
    val matchers     : Matchers,
    val equalities   : Equalities,

    val lambdas         : Seq[LambdaTemplate],
    val quantifications : Seq[QuantificationTemplate],

    val pointers : Pointers) {

    lazy val args = arguments.map(_._2)

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): TemplateContents =
      TemplateContents(
        pathVar._1 -> substituter(pathVar._2),
        arguments, condVars, exprVars, chooseVars, condTree,
        clauses.map(substituter),
        blockers.map { case (b, fis) => substituter(b) -> fis.map(_.substitute(substituter, msubst)) },
        applications.map { case (b, apps) => substituter(b) -> apps.map(_.substitute(substituter, msubst)) },
        matchers.map { case (b, ms) => substituter(b) -> ms.map(_.substitute(substituter, msubst)) },
        equalities.map { case (b, eqs) => substituter(b) -> eqs.map(_.substitute(substituter)) },
        lambdas.map(_.substitute(substituter, msubst)),
        quantifications.map(_.substitute(substituter, msubst)),
        pointers.map(p => substituter(p._1) -> substituter(p._2))
      )

    def substitution(aVar: Encoded, args: Seq[Arg]): (Clauses, Map[Encoded, Arg]) =
      substitution(aVar, (this.args zip args).toMap + (pathVar._2 -> Left(aVar)))

    def substitution(aVar: Encoded, substMap: Map[Encoded, Arg]): (Clauses, Map[Encoded, Arg]) =
      Template.substitution(condVars, exprVars, chooseVars, condTree, lambdas, quantifications, pointers, substMap, aVar)

    def instantiate(substMap: Map[Encoded, Arg]): Clauses =
      Template.instantiate(clauses, blockers, applications, matchers, equalities, substMap)

    def merge(
      condVars   : Map[Variable, Encoded],
      exprVars   : Map[Variable, Encoded],
      chooseVars : Map[Variable, Encoded],
      condTree   : Map[Variable, Set[Variable]],
      clauses      : Clauses,
      blockers     : Calls,
      applications : Apps,
      matchers     : Matchers,
      equalities   : Equalities,
      lambdas         : Seq[LambdaTemplate],
      quantifications : Seq[QuantificationTemplate],
      pointers : Pointers
    ): TemplateContents = TemplateContents(
      pathVar,
      arguments,
      this.condVars ++ condVars,
      this.exprVars ++ exprVars,
      this.chooseVars ++ chooseVars,
      this.condTree merge condTree,
      this.clauses ++ clauses,
      this.blockers merge blockers,
      this.applications merge applications,
      this.matchers merge matchers,
      this.equalities merge equalities,
      this.lambdas ++ lambdas,
      this.quantifications ++ quantifications,
      this.pointers ++ pointers
    )
  }

  trait Template { self =>
    val contents: TemplateContents

    lazy val start = contents.pathVar._2

    def instantiate(aVar: Encoded, args: Seq[Arg]): Clauses = {
      val (clauses, substMap) = contents.substitution(aVar, args)
      clauses ++ instantiate(substMap)
    }

    protected def instantiate(substMap: Map[Encoded, Arg]): Clauses = {
      contents.instantiate(substMap)
    }

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
      * [[Template.instantiate]] that is required for [[dependencies]] to make sense in the solver
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
      val (substClauses, substMap) = contents.substitution(contents.pathVar._2, Map.empty[Encoded, Arg])
      val tmplClauses = contents.instantiate(substMap)
      val instantiation = substClauses ++ tmplClauses

      val substituter = mkSubstituter(substMap.mapValues(_.encoded))
      val deps = dependencies.map(substituter)
      val key = (body, blockerPath(contents.pathVar._2), deps)

      val sortedDeps = exprOps.variablesOf(body).toSeq.sortBy(_.id.uniqueName)
      val locals = sortedDeps zip deps
      (key, instantiation, locals, substMap.mapValues(_.encoded))
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

  private[unrolling] def mkApplication(caller: Expr, args: Seq[Expr]): Expr = caller.getType match {
    case FunctionType(from, to) =>
      val (curr, next) = args.splitAt(from.size)
      mkApplication(Application(caller, curr), next)
    case _ =>
      assert(args.isEmpty, s"Non-function typed $caller applied to ${args.mkString(",")}")
      caller
  }

  object Template {

    def lambdaPointers(encoder: Expr => Encoded)(expr: Expr): Map[Encoded, Encoded] = {
      def collectSelectors(expr: Expr, ptr: Expr): Seq[(Expr, Variable)] = expr match {
        case ADT(tpe, es) => (tpe.getADT.toConstructor.fields zip es).flatMap {
          case (vd, e) =>
            val ex = if (ptr.getType == tpe) ptr else AsInstanceOf(ptr, tpe)
            collectSelectors(e, ADTSelector(ex, vd.id))
        }

        case Tuple(es) => es.zipWithIndex.flatMap {
          case (e, i) => collectSelectors(e, TupleSelect(ptr, i + 1))
        }

        case IsTyped(v: Variable, _: FunctionType) => Seq(ptr -> v)
        case _ => Seq.empty
      }

      val pointers = exprOps.collect {
        case Equals(v @ (_: Variable | _: FunctionInvocation | _: Application), e) => collectSelectors(e, v).toSet
        case Equals(e, v @ (_: Variable | _: FunctionInvocation | _: Application)) => collectSelectors(e, v).toSet
        case FunctionInvocation(_, _, es) => es.flatMap(e => collectSelectors(e, e)).toSet
        case Application(_, es) => es.flatMap(e => collectSelectors(e, e)).toSet
        case e: Tuple => collectSelectors(e, e).toSet
        case e: ADT => collectSelectors(e, e).toSet
        case _ => Set.empty[(Expr, Variable)]
      } (expr).toMap

      pointers.map(p => encoder(p._1) -> encoder(p._2))
    }

    def extractCalls(
      expr: Expr,
      substMap: Map[Variable, Encoded] = Map.empty[Variable, Encoded],
      optCall: Option[Call] = None,
      optApp: Option[App] = None
    ): (Set[Call], Set[App], Set[Matcher], Pointers) = {
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

            Some(expr -> Matcher(Left(encoder(c) -> bestRealType(c.getType)), encodedArgs, encoder(expr)))
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

      val calls = firstOrderCallsOf(expr).map { case (id, tps, args) =>
        Call(getFunction(id, tps), args.map(encodeArg))
      }.filter(i => Some(i) != optCall)

      val apps = firstOrderAppsOf(expr).filter {
        case (c, Seq(e1, e2)) => c != equalitySymbol(e1.getType)._1
        case _ => true
      }.map { case (c, args) =>
        val tpe = bestRealType(c.getType).asInstanceOf[FunctionType]
        App(encoder(c), tpe, args.map(encodeArg), encoder(mkApplication(c, args)))
      }.filter(i => Some(i) != optApp)

      val matchers = exprToMatcher.values.toSet
        .filter(i => Some(i.encoded) != optApp.map(_.encoded))
        .filter {
          case Matcher(Right(tfd), args, _) => Some(Call(tfd, args)) != optCall
          case _ => true
        }

      (calls, apps, matchers, pointers)
    }

    def encode(
      pathVar: (Variable, Encoded),
      arguments: Seq[(Variable, Encoded)],
      tmplClauses: TemplateClauses,
      substMap: Map[Variable, Encoded] = Map.empty[Variable, Encoded],
      optCall: Option[TypedFunDef] = None,
      optApp: Option[(Encoded, FunctionType)] = None
    ): (Clauses, Calls, Apps, Matchers, Pointers, () => String) = {
      val (condVars, exprVars, chooseVars, condTree, guardedExprs, eqs, equalities, lambdas, quants) = tmplClauses

      val idToTrId : Map[Variable, Encoded] =
        condVars ++ exprVars ++ chooseVars + pathVar ++ arguments ++ substMap ++
        lambdas.map(_.ids) ++ quants.flatMap(_.mapping) ++ equalities.flatMap(_._2.map(_.symbols))
      val encoder: Expr => Encoded = mkEncoder(idToTrId)

      val optIdCall = optCall.map { tfd => Call(tfd, arguments.map(p => Left(p._2))) }
      val optIdApp = optApp.map { case (idT, tpe) =>
        val encoded = mkFlatApp(idT, tpe, arguments.map(_._2))
        App(idT, bestRealType(tpe).asInstanceOf[FunctionType], arguments.map(p => Left(p._2)), encoded)
      }

      val (clauses, blockers, applications, matchers, pointers) = {
        var clauses      : Clauses = Seq.empty
        var blockers     : Map[Encoded, Set[Call]]     = Map.empty
        var applications : Map[Encoded, Set[App]]      = Map.empty
        var matchers     : Map[Encoded, Set[Matcher]]  = Map.empty
        var pointers     : Map[Encoded, Encoded]       = Map.empty

        val pv = pathVar._1
        for ((b,es) <- guardedExprs merge Map(pv -> eqs)) {
          var calls  : Set[Call]     = Set.empty
          var apps   : Set[App]      = Set.empty
          var matchs : Set[Matcher]  = Set.empty
          val bp = idToTrId(b)

          for (e <- es) {
            val (eCalls, eApps, eMatchers, ePtrs) = extractCalls(e, idToTrId, optIdCall, optIdApp)
            calls ++= eCalls
            apps ++= eApps
            matchs ++= eMatchers
            pointers ++= ePtrs
          }

          if (calls.nonEmpty) blockers += bp -> calls
          if (apps.nonEmpty) applications += bp -> apps
          if (matchs.nonEmpty) matchers += bp -> matchs
        }

        clauses ++= (for ((b,es) <- guardedExprs; e <- es) yield encoder(Implies(b, e)))
        clauses ++= eqs.map(encoder)

        (clauses, blockers, applications, matchers, pointers)
      }

      val stringRepr : () => String = () => {
        " * Activating boolean : " + pathVar._1.asString + "\n" +
        " * Control booleans   : " + condVars.keys.map(_.asString).mkString(", ") + "\n" +
        " * Expression vars    : " + exprVars.keys.map(_.asString).mkString(", ") + "\n" +
        " * Choose vars        : " + chooseVars.keys.map(_.asString).mkString(", ") + "\n" +
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
        " * Lambdas            :\n" + lambdas.map { case template =>
          " +> " + template.toString.split("\n").mkString("\n    ") + "\n"
        }.mkString("\n") +
        " * Foralls            :\n" + quants.map { case template =>
          " +> " + template.toString.split("\n").mkString("\n    ") + "\n"
        }.mkString("\n")
      }

      (clauses, blockers, applications, matchers, pointers, stringRepr)
    }

    def contents(
      pathVar: (Variable, Encoded),
      arguments: Seq[(Variable, Encoded)],
      tmplClauses: TemplateClauses,
      substMap: Map[Variable, Encoded] = Map.empty,
      optCall: Option[TypedFunDef] = None,
      optApp: Option[(Encoded, FunctionType)] = None
    ): (TemplateContents, () => String) = {

      val (condVars, exprVars, chooseVars, condTree, equalities, lambdas, quants) = tmplClauses.proj
      val (clauses, blockers, applications, matchers, pointers, string) = Template.encode(
        pathVar, arguments, tmplClauses, substMap = substMap, optCall = optCall, optApp = optApp)

      val contents = TemplateContents(
        pathVar, arguments, condVars, exprVars, chooseVars, condTree,
        clauses, blockers, applications, matchers, equalities,
        lambdas, quants, pointers
      )

      (contents, string)
    }

    def substitution(
      condVars: Map[Variable, Encoded],
      exprVars: Map[Variable, Encoded],
      chooseVars: Map[Variable, Encoded],
      condTree: Map[Variable, Set[Variable]],
      lambdas: Seq[LambdaTemplate],
      quants: Seq[QuantificationTemplate],
      pointers: Map[Encoded, Encoded],
      baseSubst: Map[Encoded, Arg],
      aVar: Encoded
    ): (Clauses, Map[Encoded, Arg]) = {

      val freshSubst = exprVars.map { case (v, vT) => vT -> encodeSymbol(v) } ++
                       chooseVars.map { case (v, vT) => vT -> encodeSymbol(v) } ++
                       freshConds(aVar, condVars, condTree)

      val matcherSubst = baseSubst.collect { case (c, Right(m)) => c -> m }

      var subst = freshSubst.mapValues(Left(_)) ++ baseSubst
      var clauses : Clauses = Seq.empty

      for ((v, vT) <- chooseVars) {
        clauses ++= registerSymbol(aVar, freshSubst(vT), v.tpe)
      }

      // /!\ CAREFUL /!\
      // We have to be wary while computing the lambda subst map since lambdas can
      // depend on each other. However, these dependencies cannot be cyclic so it
      // suffices to make sure the traversal order is correct.
      var seen : Set[LambdaTemplate] = Set.empty

      val lambdaKeys = lambdas.map(lambda => lambda.ids._2 -> lambda).toMap
      def extractSubst(lambda: LambdaTemplate): Unit = {
        for {
          dep <- lambda.closures flatMap lambdaKeys.get
          if !seen(dep)
        } extractSubst(dep)

        if (!seen(lambda)) {
          val substMap = subst.mapValues(_.encoded)
          val substLambda = lambda.substitute(mkSubstituter(substMap), matcherSubst)
          val (idT, cls) = instantiateLambda(substLambda)
          subst += lambda.ids._2 -> Left(idT)
          clauses ++= cls
          seen += lambda
        }
      }

      for (l <- lambdas) extractSubst(l)

      // instantiate positive quantifications last to avoid introducing
      // extra quantifier instantiations that arise due to empty domains
      for (q <- quants.sortBy(_.polarity.isInstanceOf[Positive])) {
        val substMap = subst.mapValues(_.encoded)
        val substQuant = q.substitute(mkSubstituter(substMap), matcherSubst)
        val (map, cls) = instantiateQuantification(substQuant)
        subst ++= map.mapValues(Left(_))
        clauses ++= cls
      }

      val substituter = mkSubstituter(subst.mapValues(_.encoded))
      for ((ptr, lambda) <- pointers) {
        registerLambda(substituter(ptr), substituter(lambda))
      }

      (clauses, subst)
    }

    def instantiate(
      clauses: Clauses,
      calls: Calls,
      apps: Apps,
      matchers: Matchers,
      equalities: Equalities,
      substMap: Map[Encoded, Arg]
    ): Clauses = {

      val substituter : Encoded => Encoded = mkSubstituter(substMap.mapValues(_.encoded))
      val msubst = substMap.collect { case (c, Right(m)) => c -> m }

      val allClauses = new scala.collection.mutable.ListBuffer[Encoded]
      allClauses ++= clauses.map(substituter)

      for ((b, fis) <- calls if !abort; bp = substituter(b); fi <- fis if !abort) {
        allClauses ++= instantiateCall(bp, fi.substitute(substituter, msubst))
      }

      for ((b,fas) <- apps if !abort; bp = substituter(b); fa <- fas if !abort) {
        allClauses ++= instantiateApp(bp, fa.substitute(substituter, msubst))
      }

      for ((b, matchs) <- matchers if !abort; bp = substituter(b); m <- matchs if !abort) {
        allClauses ++= instantiateMatcher(bp, m.substitute(substituter, msubst))
      }

      for ((b, eqs) <- equalities if !abort; bp = substituter(b); e <- eqs if !abort) {
        allClauses ++= instantiateEquality(bp, e.substitute(substituter))
      }

      allClauses.toSeq
    }
  }

  def instantiateExpr(expr: Expr, bindings: Map[Variable, Encoded]): Clauses = {
    val start = Variable.fresh("start", BooleanType, true)
    val encodedStart = encodeSymbol(start)

    val tpeClauses = bindings.flatMap { case (v, s) => registerSymbol(encodedStart, s, v.getType) }.toSeq

    val timer = timers.solvers.simplify.start()
    val instExpr = simplifyFormula(expr)
    timer.stop()

    val tmplClauses = mkClauses(start, instExpr, bindings + (start -> encodedStart), polarity = Some(true))

    val (clauses, calls, apps, matchers, pointers, _) =
      Template.encode(start -> encodedStart, bindings.toSeq, tmplClauses)

    val (condVars, exprVars, chooseVars, condTree, equalities, lambdas, quants) = tmplClauses.proj
    val (substClauses, substMap) = Template.substitution(
      condVars, exprVars, chooseVars, condTree, lambdas, quants, pointers, Map.empty, encodedStart)

    val templateClauses = Template.instantiate(clauses, calls, apps, matchers, equalities, substMap)
    val allClauses = encodedStart +: (tpeClauses ++ substClauses ++ templateClauses)

    for (cl <- allClauses) {
      reporter.debug("  . " + cl)
    }

    allClauses
  }
}
