/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import evaluators._

import scala.util.boundary
import scala.util.boundary._
import scala.collection.immutable.{ListSet, VectorMap}
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, Queue}

trait QuantificationTemplates { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import quantificationsManager.{axioms, deferred, matcherBlockers, substBlockers, templates, state, updateDeferred}

  /* -- Extraction helpers -- */

  object QuantificationMatcher {
    // @nv: no need to match on FiniteMap and FiniteSet as
    //      simplifyMatchers in SymbolOps will transform them to MapUpdated
    //      and SetAdd (which generate matchers)
    def unapply(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case Application(e, args) => Some(e -> args)
      case MapApply(map, key) => Some(map -> Seq(key))
      case MapUpdated(map, key, value) => Some(map -> Seq(key))
      case MultiplicityInBag(elem, bag) => Some(bag -> Seq(elem))
      case bag @ FiniteBag(Seq((key, _)), _) => Some(bag -> Seq(key))
      case BagAdd(bag, elem) => Some(bag -> Seq(elem))
      case ElementOfSet(elem, set) => Some(set -> Seq(elem))
      case SetAdd(set, elem) => Some(set -> Seq(elem))
      case _ => None
    }
  }

  object FunctionMatcher {
    def unapply(expr: Expr): Option[(TypedFunDef, Seq[Expr])] = expr match {
      case fi @ FunctionInvocation(_, _, args) => Some((fi.tfd, args))
      case _ => None
    }
  }

  private def matcherArgumentTypes(tpe: Type): (Seq[Type], Type) = tpe match {
    case FunctionType(from, to) => from -> to
    case MapType(from, to) => Seq(from) -> to
    case BagType(base) => Seq(base) -> IntegerType()
    case SetType(base) => Seq(base) -> BooleanType()
    case _ => throw new InternalSolverError("Matcher argument type of unsupported type " + tpe.asString)
  }

  /* -- Quantifier template definitions -- */

  /** Represents the polarity of the quantification within the considered
    * formula. Positive and negative polarity enable optimizations during
    * quantifier instantiation.
    */
  sealed abstract class Polarity(val isPositive: Boolean) {
    val isNegative: Boolean = !isPositive

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): Polarity = this match {
      case Positive(subst) => Positive(subst.map(p => p._1 -> p._2.substitute(substituter, msubst)))
      case Negative(insts) => Negative(insts._1 -> substituter(insts._2))
    }
  }

  case class Positive(subst: Map[Variable, Arg]) extends Polarity(true)
  case class Negative(insts: (Variable, Encoded)) extends Polarity(false)

  class QuantificationTemplate private[QuantificationTemplates] (
    val polarity: Polarity,
    val contents: TemplateContents,
    val structure: TemplateStructure,
    val body: Expr,
    private[QuantificationTemplates] val calleeMatchers: Seq[(Encoded, Matcher)],
    stringRepr: () => String,
    private val isConcrete: Boolean,
    private[QuantificationTemplates] val isDeferred: Boolean) {

    lazy val quantifiers = contents.arguments

    lazy val start = contents.pathVar._2
    lazy val mapping: Map[Variable, Encoded] = polarity match {
      case Positive(_) => Map.empty
      case Negative(insts) => Map(insts)
    }

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]) =
      new QuantificationTemplate(
        polarity.substitute(substituter, msubst),
        contents.substitute(substituter, msubst),
        structure.substitute(substituter, msubst),
        body, calleeMatchers.map { case (b, m) => substituter(b) -> m.substitute(substituter, msubst) },
        stringRepr, isConcrete, isDeferred
      )

    def concretize: QuantificationTemplate = {
      assert(!isConcrete, "Can't concretize concrete quantification template")
      val substituter = mkSubstituter(structure.instantiationSubst)
      new QuantificationTemplate(polarity,
        contents.substitute(substituter, Map.empty),
        structure, body, calleeMatchers.map { case (b, m) => substituter(b) -> m.substitute(substituter, Map.empty) },
        stringRepr, true, isDeferred)
    }

    private lazy val str : String = stringRepr()
    override def toString : String = str
  }

  /** The matchers that the calls of the body `body` of a quantifier over `quantifiers` reach, with
    * the blockers of these calls in `contents`, the contents of the template of the quantifier.
    *
    * A call on quantified variables is a matcher of the quantifier, which is thus instantiated for
    * the values that the function is called on. The body of the function, once the call of an
    * instance is unfolded, has calls, applications and collection lookups on these values in turn,
    * which match other quantifiers, and whose own values the quantifier is not instantiated for
    * unless something else matches it. The calls on quantified variables in the body of the
    * function, and its applications and collection lookups on them, are therefore matchers of the
    * quantifier as well, and so are those of the functions of these calls in turn: the quantifier
    * is instantiated for the values that these are called and looked up on. For example,
    * {{{
    *   def contains(l: List, a: BigInt): Boolean = { ... } ensuring (_ == content(l).contains(a))
    *   forall((a: BigInt) => contains(l, a) ==> a <= x)
    * }}}
    * is instantiated for the elements that are looked up in the content of `l`, and not only for
    * those that `contains` is called on.
    *
    * These matchers are not items of the template: an instance of the quantifier doesn't contain
    * their terms, which its calls only reach once they are unfolded, and under conditions that the
    * template doesn't know. An instance adds them as ground matchers in the generation after its
    * own (see [[Axiom.instantiateSubst]]).
    *
    * Only the calls whose arguments are all variables of the quantifier (quantified or free) are
    * taken and unfolded, of which there are finitely many, as are the applications and lookups on
    * such arguments, of functions and collections over such variables. */
  private def calleeMatchers(contents: TemplateContents, body: Expr, quantifiers: Set[Variable],
                             subst: Map[Variable, Encoded]): Seq[(Encoded, Matcher)] = {
    val encoder = mkEncoder(subst)
    def quantified(args: Seq[Expr]): Boolean = args.exists { case v: Variable => quantifiers(v) case _ => false }
    def variables(args: Seq[Expr]): Boolean = args.forall { case v: Variable => subst.contains(v) case _ => false }

    // The calls, applications and collection lookups that the call `root` of the body reaches, in
    // order of occurrence
    def reached(root: FunctionInvocation): Seq[Expr] = {
      val seen = scala.collection.mutable.LinkedHashSet[Expr]()
      // a function is unfolded once for given arguments, whatever its type arguments are: there
      // are finitely many functions and tuples of variables, also when the recursion is polymorphic
      val unfolded = scala.collection.mutable.Set[(Identifier, Seq[Expr])]()
      def unfold(fi: FunctionInvocation): Unit = {
        val tfd = fi.tfd
        val result = tfd.applied(tfd.params.map(_.toVariable))
        // the refinements of the return type say of the result what a postcondition in the body would
        for (e <- tfd.fullBody +: typeOps.refinements(tfd.returnType, result)._2) exprOps.preTraversal {
          case call: FunctionInvocation if quantified(call.args) && variables(call.args) =>
            seen += call
            if (unfolded.add(call.id -> call.args)) unfold(call)
          case e @ QuantificationMatcher(c, args) if quantified(args) && variables(args) &&
            exprOps.variablesOf(c).forall(subst.contains) => seen += e
          case _ =>
        } (tfd.withParamSubst(fi.args, e))
      }
      unfold(root)
      seen.toSeq
    }

    val roots = exprOps.collectPreorder[FunctionInvocation] {
      case fi: FunctionInvocation if quantified(fi.args) => Seq(fi)
      case _ => Seq.empty
    } (body).distinct

    val known = contents.items.matchers.values.flatten.toSet
    (for {
      root <- roots
      matchers = reached(root).map {
        case call @ FunctionInvocation(_, _, args) =>
          Matcher(Right(call.tfd), args.map(arg => Left(encoder(arg))), encoder(call))
        case e @ QuantificationMatcher(c, args) =>
          Matcher(Left(encoder(c) -> c.getType), args.map(arg => Left(encoder(arg))), encoder(e))
      }.filterNot(known)
      if matchers.nonEmpty
      // The call is found by its arguments when they are variables, and by its function otherwise.
      // A call whose matcher is not in these contents (one under a lambda or another quantifier,
      // which has a template of its own) adds nothing here.
      rootArgs = if (variables(root.args)) Some(root.args.map(arg => Left(encoder(arg)))) else None
      (b, ms) <- contents.items.matchers.toSeq
      if ms.exists(m => m.key == Right(root.tfd) && rootArgs.forall(_ == m.args))
      matcher <- matchers
    } yield b -> matcher).distinct
  }

  object QuantificationTemplate {
    def apply(
      pathVar: (Variable, Encoded),
      pol: Boolean,
      forall: Forall,
      substMap: Map[Variable, Encoded],
      defer: Boolean = false
    ): (Expr, QuantificationTemplate) = {
      val (Forall(args, body), structure, depSubst) =
        mkExprStructure(pathVar._1, forall, substMap): @unchecked

      val quantifiers = args.map(_.toVariable).toSet
      val idQuantifiers: Seq[Variable] = args.map(_.toVariable)
      val trQuantifiers: Seq[Encoded] = forall.params.map(v => encodeSymbol(v.toVariable))

      val clauseSubst: Map[Variable, Encoded] = depSubst ++ (idQuantifiers zip trQuantifiers)
      val (p, tmplClauses) = mkExprClauses(pathVar._1, body, clauseSubst)

      given TypingGenerator = if (pol) ContractGenerator else FreeGenerator
      val (tpeCond, tpeClauses) = idQuantifiers.foldLeft((BooleanLiteral(true): Expr, TemplateClauses())) {
        case ((tpCond, tpClauses), v) =>
          val (p, clauses) = mkTypeClauses(pathVar._1, v.tpe, v, clauseSubst, inDomain = true)
          (and(tpCond, p), tpClauses ++ clauses)
      }

      val clauses: TemplateClauses = tmplClauses ++ tpeClauses
      // the body holds of the quantified values that lie in their types
      val domain = andJoin(idQuantifiers.map(v => typingMarker(typingMode(summon[TypingGenerator], true, false), v.tpe, v)))
      val (res, polarity, contents, str) = if (pol) {
        val subst = quantifiers.flatMap(v => typeOps.variablesOf(v.tpe)).map(v => v -> Left(clauseSubst(v))).toMap

        val (contents, str) = Template.contents(pathVar, idQuantifiers zip trQuantifiers,
          clauses + (pathVar._1 -> Implies(tpeCond, p)), depSubst, source = Some((None, Implies(domain, body))))

        (BooleanLiteral(true), Positive(subst), contents, str)
      } else {
        val inst = Variable.fresh("inst", BooleanType(), true)
        val instT = encodeSymbol(inst)

        val (contents, str) = Template.contents(pathVar, idQuantifiers zip trQuantifiers,
          clauses + (pathVar._1 -> Equals(inst, Implies(tpeCond, p))), depSubst + (inst -> instT),
          source = Some((None, Equals(inst, Implies(domain, body)))))

        (inst, Negative(inst -> instT), contents, str)
      }

      val template = new QuantificationTemplate(polarity, contents, structure, body,
        calleeMatchers(contents, body, quantifiers, clauseSubst),
        () => "Template for " + forall.asString + " is :\n" + str(), false, defer)

      (res, template)
    }
  }

  /** The instantiations that are deferred to a later generation, with the generation at which
    * each one is due:
    *  - the matchers that the instantiation of an axiom reaches under a blocker other than its
    *    guard;
    *  - the substitutions of axioms that their cost delays (see [[Axiom.instantiate]]);
    *  - the axioms whose quantifiers may still have no ground (see [[Axiom.ensureGrounds]]).
    *
    * While some are pending, a model is only accepted once the finite range check shows that they
    * add nothing to it (see [[getFiniteRangeClauses]]). Each kind is kept in the order in which it
    * was deferred, and the substitutions of an axiom are a set (the keys of a [[VectorMap]]). */
  private[unrolling] case class Deferred(
    matchers: Vector[(Int, Set[Encoded], Matcher)],
    substs: VectorMap[Axiom, VectorMap[(Int, Set[Encoded], Map[Encoded, Arg]), Unit]],
    grounds: VectorMap[Int, Set[Axiom]]) {

    def isEmpty: Boolean = grounds.isEmpty && matchers.isEmpty && !substs.exists(_._2.nonEmpty)

    /** The earliest generation at which a deferred instantiation is due. */
    def generation: Option[Int] = {
      val gens: Seq[Int] = matchers.map(_._1) ++
        substs.toSeq.flatMap(p => p._2.keys.map(_._1)) ++
        grounds.keys
      if (gens.isEmpty) None else Some(gens.min)
    }

    /** All the deferred instantiations, due `diff` generations earlier. */
    def advance(diff: Int): Deferred = Deferred(
      matchers.map { case (gen, bs, m) => (gen - diff, bs, m) },
      substs.map { case (q, ss) => q -> ss.map { case ((gen, bs, subst), u) => ((gen - diff, bs, subst), u) } },
      grounds.map { case (gen, qs) => (gen - diff) -> qs })

    def deferMatcher(gen: Int, blockers: Set[Encoded], matcher: Matcher): Deferred =
      copy(matchers = matchers :+ ((gen, blockers, matcher)))

    /** Without the first occurrence of `entry`. */
    def removeMatcher(entry: (Int, Set[Encoded], Matcher)): Deferred = {
      val i = matchers.indexOf(entry)
      if (i < 0) this else copy(matchers = matchers.patch(i, Nil, 1))
    }

    def deferSubst(axiom: Axiom, gen: Int, blockers: Set[Encoded], subst: Map[Encoded, Arg]): Deferred =
      copy(substs = substs.updated(axiom, substs.getOrElse(axiom, VectorMap.empty).updated((gen, blockers, subst), ())))
    def hasSubsts(axiom: Axiom): Boolean = substs.contains(axiom)
    def substsOf(axiom: Axiom): Seq[(Int, Set[Encoded], Map[Encoded, Arg])] = substs(axiom).keys.toSeq

    /** The substitutions of `axiom` that are due, and the deferred instantiations without them. */
    def releaseSubsts(axiom: Axiom): (Seq[(Int, Set[Encoded], Map[Encoded, Arg])], Deferred) = {
      val (release, keep) = substs(axiom).partition(_._1._1 <= currentGeneration)
      (release.keys.toSeq, copy(substs = substs.updated(axiom, keep)))
    }

    def deferGrounds(gen: Int, axiom: Axiom): Deferred =
      copy(grounds = grounds.updated(gen, ListSet.from(grounds.getOrElse(gen, ListSet.empty)) + axiom))
    def removeGrounds(gen: Int, axiom: Axiom): Deferred = {
      val remaining = grounds.getOrElse(gen, ListSet.empty) - axiom
      copy(grounds = if (remaining.nonEmpty) grounds.updated(gen, remaining) else grounds - gen)
    }

    /** With the grounds of `axioms`, which are due at `gen`, due at the current generation instead. */
    def postponeGrounds(gen: Int, axioms: Set[Axiom]): Deferred =
      copy(grounds = (grounds - gen).updated(currentGeneration, axioms))
  }

  private object Deferred {
    val empty: Deferred = Deferred(Vector.empty, VectorMap.empty, VectorMap.empty)
  }

  /** The state of an axiom (see [[Axiom]]).
    *
    * @param grounds the ground values of each quantifier, with their blockers and abstract
    *                generations (see [[Ground]])
    * @param instantiations the blockers of the calls and applications of each instantiation of
    *                       the axiom, by its enabler, which a model that falsifies the
    *                       instantiation promotes */
  private[unrolling] case class AxiomState(
    grounds: Map[Encoded, VectorMap[Arg, (Set[Encoded], Set[Int])]],
    instantiations: VectorMap[Encoded, Set[Encoded]])

  private object AxiomState {
    val empty: AxiomState = AxiomState(Map.empty, VectorMap.empty)
  }

  /** The state of [[quantificationsManager]], which push saves and pop restores as a whole. The
    * maps and the sets that are iterated keep their insertion order, so that the clauses don't
    * depend on hash codes (see [[Items]]).
    *
    * @param axioms the axioms, in the order in which they were instantiated
    * @param axiomStates the state of each axiom
    * @param matcherBlockers the blocker of each instantiated matcher
    * @param waitingMatchers the blockers that enable the blocker of a matcher, whose clauses wait for
    *                        the first axiom (see [[instantiateMatcher0]])
    * @param substBlockers the blocker of each instantiated substitution of an axiom
    * @param templates the instantiated quantifications, by structure, with their result
    * @param deferred the instantiations that are deferred to a later generation */
  private[unrolling] case class QuantificationsState(
    axioms: Vector[Axiom],
    axiomStates: Map[Axiom, AxiomState],
    matcherBlockers: VectorMap[Matcher, Encoded],
    waitingMatchers: Vector[(Encoded, Encoded)],
    substBlockers: VectorMap[(Axiom, Map[Encoded, Arg]), Encoded],
    templates: VectorMap[TemplateStructure, (QuantificationTemplate, Encoded)],
    deferred: Deferred)

  private object QuantificationsState {
    val empty: QuantificationsState =
      QuantificationsState(Vector.empty, Map.empty, VectorMap.empty, Vector.empty, VectorMap.empty, VectorMap.empty, Deferred.empty)
  }

  private[unrolling] object quantificationsManager extends Manager {
    private[QuantificationTemplates] val state = new Snapshots(QuantificationsState.empty)

    private[QuantificationTemplates] def axioms: Vector[Axiom] = state.get.axioms
    private[QuantificationTemplates] def matcherBlockers: VectorMap[Matcher, Encoded] = state.get.matcherBlockers
    private[QuantificationTemplates] def substBlockers: VectorMap[(Axiom, Map[Encoded, Arg]), Encoded] = state.get.substBlockers
    private[QuantificationTemplates] def templates: VectorMap[TemplateStructure, (QuantificationTemplate, Encoded)] = state.get.templates
    private[QuantificationTemplates] def deferred: Deferred = state.get.deferred
    private[QuantificationTemplates] def updateDeferred(f: Deferred => Deferred): Unit =
      state.update(s => s.copy(deferred = f(s.deferred)))

    val incrementals: Seq[IncrementalState] = Seq(state)

    override def satisfactionAssumptions = Seq()
    override def refutationAssumptions = Seq()

    def unrollGeneration: Option[Int] = deferred.generation

    // promoting blockers makes no sense in this context
    def promoteBlocker(b: Encoded): Boolean = false

    /** Instantiates the deferred matchers, substitutions and grounds that are due, in that order,
      * and stops between them when the solver is interrupted. */
    def unroll: Clauses = {
      val matcherClauses = debugged("matchers", unrollMatchers())
      if (interrupted) return matcherClauses

      val substClauses = debugged("substitutions", unrollSubsts())
      if (interrupted) return matcherClauses ++ substClauses

      matcherClauses ++ substClauses ++ debugged("grounds", unrollGrounds())
    }

    private def debugged(kind: String, clauses: Clauses): Clauses = {
      reporter.debug("Unrolling deferred " + kind + " (" + clauses.size + ")")
      for (cl <- clauses) {
        reporter.debug("  . " + cl)
      }
      clauses
    }

    private def unrollMatchers(): Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      for (e @ (gen, bs, m) <- deferred.matchers if gen <= currentGeneration && !interrupted) {
        clauses ++= instantiateMatcher0(bs, m, defer = true)
        updateDeferred(_.removeMatcher(e))
      }
      clauses.toSeq
    }

    private def unrollSubsts(): Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      for (q <- axioms if deferred.hasSubsts(q) && !interrupted) {
        val (release, rest) = deferred.releaseSubsts(q)
        updateDeferred(_ => rest)
        // an axiom can have hundreds of due substitutions, so an interruption stops between them
        for ((gen, bs, subst) <- release) {
          if (interrupted) updateDeferred(_.deferSubst(q, gen, bs, subst))
          else clauses ++= q.instantiateSubst(bs, subst, defer = true)
        }
      }
      clauses.toSeq
    }

    private def unrollGrounds(): Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      for ((gen, qs) <- deferred.grounds.toList if gen <= currentGeneration && !interrupted; q <- qs if !interrupted) {
        clauses ++= q.ensureGrounds
        updateDeferred(_.removeGrounds(gen, q))
      }
      clauses.toSeq
    }
  }

  // Due to a Scala 3 bug, if we name the following two methods the same, we encounter a strange error.
  // The following open ticket should be related to our problems:
  // https://github.com/lampepfl/dotty/issues/11226
  def instantiateMatcher(blocker: Encoded, matcher: Matcher): Clauses = {
    // first instantiate sub-matchers
    val subs = matcher.args.collect { case Right(m) =>
      instantiateMatcher0(Set(blocker), m, false)
    }.flatten

    subs ++ instantiateMatcher0(Set(blocker), matcher, false)
  }

  private def instantiateMatcher0(blockers: Set[Encoded], matcher: Matcher, defer: Boolean = false): Clauses = {
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]

    val matcherBlocker = matcherBlockers.get(matcher) match {
      case Some(matcherBlocker) =>
        matcherBlocker

      case None =>
        val matcherBlocker = encodeSymbol(Variable.fresh("m", BooleanType(), true))
        state.update(s => s.copy(matcherBlockers = s.matcherBlockers.updated(matcher, matcherBlocker)))

        reporter.debug(" -> instantiating matcher " + matcherBlocker + " ==> " + matcher)
        for (q <- axioms) clauses ++= q.instantiate(matcherBlocker, matcher, defer)

        matcherBlocker
    }

    if (blockers != Set(matcherBlocker)) {
      val (blocker, blockerClauses) = encodeBlockers(blockers)
      registerImplication(blocker, matcherBlocker)
      clauses ++= blockerClauses
      // The blocker of a matcher guards the instances of the axioms, and tells which applications
      // of a function belong to a model. Until there is an axiom, the blockers of the calls to
      // named functions are thus not looked at, and the clauses that enable them wait for one.
      if (axioms.isEmpty && matcher.key.isRight) {
        state.update(s => s.copy(waitingMatchers = s.waitingMatchers :+ (blocker -> matcherBlocker)))
      } else {
        clauses ++= enables(blocker, matcherBlocker)
      }
    }

    clauses.toSeq
  }

  protected def hasAxioms: Boolean = axioms.nonEmpty
  protected def getAxioms: Seq[Axiom] = axioms.toSeq

  protected def getInstantiationsWithBlockers: Seq[(Encoded, Set[Encoded])] = axioms.flatMap(_.instantiations.toSeq)
  protected def hasInstantiationsWithBlockers = axioms.exists(_.instantiations.nonEmpty)

  protected sealed trait MatcherKey
  private case class FunctionKey(tfd: TypedFunDef) extends MatcherKey
  // Having an abstract class (instead of a sealed trait) causes a NoSuchMethodError in getGroundInstantiations.
  // This is surely a bug in Scala 3.
  private sealed trait TypedKey(val tpe: Type) extends MatcherKey
  private case class LambdaKey(lambda: Lambda, tt: Type) extends TypedKey(tt)
  private case class CallerKey(caller: Encoded, tt: FunctionType) extends TypedKey(tt)
  private case class TypeKey(tt: Type) extends TypedKey(tt)

  private def matcherKey(key: Either[(Encoded, Type), TypedFunDef]): MatcherKey = key match {
    case Right(tfd) =>
      FunctionKey(tfd)
    case Left((caller, ft: FunctionType)) => lambdaTemplate(caller) match {
      case Some(template) => LambdaKey(template.structure.body.asInstanceOf[Lambda], ft)
      case None => CallerKey(caller, ft)
    }
    case Left((_, tpe)) =>
      TypeKey(tpe)
  }

  @inline
  private def matcherKey(m: Matcher): MatcherKey = matcherKey(m.key)

  protected def correspond(k1: MatcherKey, k2: MatcherKey): Option[Boolean] = (k1, k2) match {
    case (`k2`, _) => Some(true)
    case (tp1: TypedKey, tp2: TypedKey) if tp1.tpe == tp2.tpe => Some(false)
    case _ => None
  }

  /** Ground values are annotated with an {{{Set[Int]}}} value that specifies
    * the (optional) abstract generations at which this instantiation was added to the set.
    * The abstract generations exist iff the matchers do not exactly correspond (for example,
    * abstract matcher {{{f(x)}}} instantiated against concrete application {{{g(1)}}}).
    *
    * Instantiating {{{f(x)}}} against {{{f(1)}}} will lead to an EMPTY abstract generation set.
    *
    * If we see an {{{f(1)}}} instantiation and had some abstract instantiation corresponding
    * to {{{g(1)}}} in our set of instantiations, we can forget about {{{g(1)}}} as {{{f(1)}}}
    * is "more certain". If we see {{{h(1)}}} and had {{{g(1)}}}, we can merge the two sets
    * (see [[Axiom.addGround]]).
    */
  /** A ground value `arg` of a quantifier under the blockers `blockers`, with its abstract
    * generations (see [[GroundSet]]). */
  private case class Ground(blockers: Set[Encoded], arg: Arg, gens: Set[Int])

  /** A substitution of some of the quantifiers of an axiom under `blockers`, with the abstract
    * generations of its grounds and the number of generations by which it is delayed. */
  private case class Partial(blockers: Set[Encoded], subst: Map[Encoded, Arg], gens: Set[Int], delay: Int)

  /** A substitution of all the quantifiers of an axiom under `blockers`, which is instantiated
    * `delay` generations from now. */
  private case class Candidate(blockers: Set[Encoded], subst: Map[Encoded, Arg], delay: Int)

  /** Extends `partial` to the quantifiers `rest`, with each of their grounds. A ground delays the
    * substitution by one generation unless it is exact or shares an abstract generation with it. */
  private def extend(partial: Partial, rest: Set[Encoded], grounds: Map[Encoded, Set[Ground]]): Seq[Partial] =
    rest.foldLeft(Seq(partial)) { (partials, q) =>
      for {
        p <- partials
        Ground(bs, arg, gens) <- grounds.getOrElse(q, Set.empty[Ground]).toSeq
      } yield {
        val delay = if (gens.isEmpty || (p.gens intersect gens).nonEmpty) 0 else 1
        Partial(ListSet.from(p.blockers) ++ bs, p.subst + (q -> arg), p.gens ++ gens, p.delay + delay)
      }
    }

  private def totalDepth(m: Matcher): Int = 1 + m.args.map {
    case Right(ma) => totalDepth(ma)
    case _ => 0
  }.sum

  private def encodeEnablers(es: Set[Encoded]): Encoded =
    if (es.isEmpty) trueT else mkAnd(es.toSeq*)

  private[solvers] class Axiom(
    contents: TemplateContents,
    subst: Map[Variable, Arg],
    val body: Expr,
    calleeMatchers: Seq[(Encoded, Matcher)],
    defer: Boolean) {

    private def axiomState: AxiomState = state.get.axiomStates.getOrElse(this, AxiomState.empty)
    private def updateAxiomState(f: AxiomState => AxiomState): Unit =
      state.update(s => s.copy(axiomStates = s.axiomStates.updated(this, f(s.axiomStates.getOrElse(this, AxiomState.empty)))))

    def instantiations: VectorMap[Encoded, Set[Encoded]] = axiomState.instantiations

    private def registerBlockers(substituter: Encoded => Encoded): Unit = {
      val enabler = substituter(contents.pathVar._2)
      val bs = ListSet.from((contents.items.calls.keys ++ contents.items.apps.keys).map(substituter))
      updateAxiomState(a => a.copy(instantiations = a.instantiations.updated(enabler, bs)))
    }

    /** The ground values of `q`, in the order in which they were found. */
    private def groundsOf(q: Encoded): VectorMap[Arg, (Set[Encoded], Set[Int])] =
      axiomState.grounds.getOrElse(q, VectorMap.empty)
    private def groundSet(q: Encoded): Set[Ground] =
      ListSet.from(groundsOf(q).iterator.map { case (arg, (bs, gens)) => Ground(bs, arg, gens) })
    /** Whether `arg` is a ground value of `q` under some of the blockers `bs`. */
    private def isGround(q: Encoded, bs: Set[Encoded], arg: Arg): Boolean =
      groundsOf(q).get(arg).exists(p => p._1 subsetOf bs)

    /** Adds the ground value `g` of `q`, which merges with the ground of the same value (see [[Ground]]). */
    private def addGround(q: Encoded, g: Ground): Unit = updateAxiomState { a =>
      val gs = a.grounds.getOrElse(q, VectorMap.empty)
      val merged = gs.get(g.arg) match {
        case Some((bs, gens)) =>
          val newBs: Set[Encoded] = ListSet.from(bs) ++ g.blockers
          val newGens: Set[Int] = if (gens.isEmpty || g.gens.isEmpty) Set.empty else gens ++ g.gens
          newBs -> newGens
        case None =>
          g.blockers -> g.gens
      }
      a.copy(grounds = a.grounds.updated(q, gs.updated(g.arg, merged)))
    }

    lazy val quantifiers = contents.arguments
    lazy val quantified: Set[Encoded] = ListSet.from(quantifiers.map(_._2))
    lazy val pathBlockers = blockerPath(contents.pathVar._2)

    lazy val guard: Encoded = contents.pathVar._2

    private lazy val matchers: Matchers = contents.items.matchers

    // The axiom is instantiated for the values that its matchers match, and for those that the
    // matchers of its callees do (see [[calleeMatchers]])
    private val matching: Seq[Matcher] = matchers.flatMap(_._2).toSeq ++ calleeMatchers.map(_._2)

    private val keys: Seq[MatcherKey] = matching.map(matcherKey)
    private val constraints: Seq[(Encoded, MatcherKey, Int)] = for {
      m <- matching
      (arg,i) <- m.args.zipWithIndex
      q <- arg.left.toOption if quantified(q)
    } yield (q, matcherKey(m), i)

    // the quantifiers in the order in which their constraints occur (see [[Items]])
    private val groupedConstraints: Map[Encoded, Seq[(MatcherKey, Int)]] =
      VectorMap.from(constraints.map(_._1).distinct.map(q => q -> constraints.collect { case (`q`, key, i) => (key, i) }))

    /** The abstract generation of the last instantiation (see [[Ground]]). Like the ids of fresh
      * symbols, it only grows, and a pop doesn't reset it. */
    private var generationCounter: Int = 0

    private val optimizationQuorums: Seq[Set[Matcher]] = {
      def matchersOf(m: Matcher): Set[Matcher] = m.args.flatMap {
        case Right(m) => matchersOf(m) + m
        case _ => Set.empty[Matcher]
      }.toSet

      def quantifiersOf(m: Matcher): Set[Encoded] =
        (matchersOf(m) + m).flatMap(_.args.collect { case Left(q) if quantified(q) => q })

      val allMatchers = matchers.flatMap(_._2).toList
      val allQuorums = allMatchers.toSet.subsets()
        .filter(ms => ms.flatMap(quantifiersOf) == quantified)
        .filterNot(ms => allMatchers.exists { m =>
          !ms(m) && {
            val common = ms & matchersOf(m)
            common.nonEmpty &&
            (quantifiersOf(m) -- common.flatMap(quantifiersOf)).nonEmpty
          }
        }).toList
      allQuorums.foldLeft(Seq[Set[Matcher]]())((qs,q) => if (qs.exists(_ subsetOf q)) qs else qs :+ q)
    }

    def instantiate(b: Encoded, m: Matcher, defer: Boolean = false): Clauses = {
      if (!keys.exists(correspond(_, matcherKey(m)).nonEmpty)) return Seq.empty

      generationCounter += 1
      val gen = generationCounter

      /* Build mappings from quantifiers to all potential ground values previously encountered. */
      val quantToGround: Map[Encoded, Set[Ground]] =
        for ((q, constraints) <- groupedConstraints) yield q -> {
          groundSet(q) ++ constraints.flatMap {
            case (key, i) => correspond(matcherKey(m), key).map {
              p => Ground(Set(b), m.args(i), if (p) Set.empty[Int] else Set(gen))
            }
          }
        }

      /* Transform the map to sets into a sequence of maps making sure that the current
       * matcher is part of the mapping (otherwise, instantiation has already taken place). */
      var candidates: Seq[Candidate] = Seq.empty
      for ((q, constraints) <- groupedConstraints;
           (key, i) <- constraints;
           perfect <- correspond(matcherKey(m), key)) {
        val initGens: Set[Int] = if (perfect && !defer) Set.empty else Set(gen)
        val partials = extend(Partial(Set(b), Map(q -> m.args(i)), initGens, 0), quantified - q, quantToGround)

        /* @nv: I reused the cost heuristic from Leon here, it worked pretty well
         *      on all our pre-existing benchmarks and regressions. */
        candidates ++= partials.map { case Partial(bs, map, _, c) =>
          val cost = if (initGens.nonEmpty) {
            1 + 3 * map.values.collect { case Right(m) => totalDepth(m) }.sum
          } else {
            val substituter = mkSubstituter(map.view.mapValues(_.encoded).toMap)
            val msubst = map.collect { case (q, Right(m)) => q -> m }
            val opts = optimizationQuorums.flatMap { ms =>
              val sms = ms.map(_.substitute(substituter, msubst))
              if (sms.forall(sm => matcherBlockers.contains(sm))) sms.toList else Nil
            }

            if (opts.nonEmpty) {
              val tms = matchers.flatMap(_._2.map(_.substitute(substituter, msubst)))
              if (opts.map(totalDepth).max >= tms.map(totalDepth).max) 0
              else 3
            } else if (isGround(q, bs, m.args(i))) {
              10
            } else {
              3
            }
          }

          Candidate(bs, map, c + cost)
        }

        // register ground instantiation for future instantiations
        addGround(q, Ground(Set(b), m.args(i), initGens))
      }

      instantiateSubsts(candidates)
    }

    def hasAllGrounds: Boolean = quantified.forall(q => groundsOf(q).nonEmpty)

    def ensureGrounds: Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]

      /* Build mappings from quantifiers to all potential ground values previously encountered
       * AND the constants we're introducing to make sure grounds are non-empty. */
      val quantToGround: Map[Encoded, Set[Ground]] = (for ((v,q) <- quantifiers) yield {
        val groundsSet: Set[Ground] = groundSet(q)
        q -> (if (groundsSet.isEmpty) Set(Ground(Set(), Left(q), Set())) else groundsSet)
      }).toMap

      /* Generate the sequence of all relevant instantiation mappings */
      var candidates: Seq[Candidate] = Seq.empty
      for ((v,q) <- quantifiers if groundsOf(q).isEmpty) {
        val res: Set[Encoded] = if (FreeUnrolling `unroll` v.tpe) {
          val closures = typeOps.variablesOf(v.tpe).toSeq.sortBy(_.id).map(subst)
          val result = encodeSymbol(Variable.fresh("result", BooleanType(), true))
          // The functions of a fresh ground are only checked to lie in their types when these may be
          // empty (see `TemplateGenerator.mkTypeClauses`), as the check unfolds witness arguments.
          val ground = hasInstance(v.tpe) != Some(true)
          clauses ++= instantiateType(contents.pathVar._2, Typing(v.tpe, q, Constraint(result, closures, true, inDomain = true, ground = ground)))
          Set(result)
        } else {
          Set.empty
        }

        val partials = extend(Partial(res, Map(q -> Left(q)), Set(), 0), quantified - q, quantToGround)
        candidates ++= partials.map { case Partial(bs, map, _, c) =>
          Candidate(bs, map, c + (3 * map.values.collect { case Right(m) => totalDepth(m) }.sum))
        }

        addGround(q, Ground(res, Left(q), Set.empty[Int]))
      }

      clauses ++= instantiateSubsts(candidates)
      clauses.toSeq
    }

    private def instantiateSubsts(candidates: Seq[Candidate]): Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]

      for (Candidate(bs, subst, delay) <- candidates if !substBlockers.get(this -> subst).exists(b => Set(b) == bs)) {
        if (delay > 0) {
          updateDeferred(_.deferSubst(this, currentGeneration + delay + (if (defer) 2 else 0), bs, subst))
        } else {
          clauses ++= instantiateSubst(bs, subst, defer = false)
        }
      }

      clauses.toSeq
    }

    def instantiateSubst(bs: Set[Encoded], subst: Map[Encoded, Arg], defer: Boolean = false): Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]

      val substBlocker = substBlockers.get(this -> subst) match {
        case Some(substBlocker) =>
          substBlocker

        case None =>
          val substBlocker = encodeSymbol(Variable.fresh("s", BooleanType(), true))
          state.update(s => s.copy(substBlockers = s.substBlockers.updated(this -> subst, substBlocker)))

          val (enabler, enablerClauses) = encodeBlockers(pathBlockers + substBlocker)
          clauses ++= enablerClauses

          val baseSubst = subst + (contents.pathVar._2 -> Left(enabler))
          val instantiation = contents.instantiation(enabler, baseSubst)
          val msubst = instantiation.msubst
          val substituter = instantiation.substituter
          registerBlockers(substituter)

          // matcher instantiation must be manually controlled here to avoid never-ending loops
          clauses ++= Rule.Instance(instantiation, InstanceOf.OfAxiom).clauses

          for ((b,ms) <- matchers; m <- ms) {
            val sb = if (b == guard) bs else ListSet.from(bs) + substituter(b)
            val sm = m.substitute(substituter, msubst)

            if (b != guard) {
              updateDeferred(_.deferMatcher(currentGeneration + 1, sb, sm))
            } else {
              clauses ++= instantiateMatcher0(sb, sm, defer = defer)
            }
          }

          // The matchers of the callees are those of terms that the calls of the instance reach
          // once they are unfolded: they wait for the next generation, also under the guard
          for ((b, m) <- calleeMatchers) {
            val sb = if (b == guard) bs else ListSet.from(bs) + substituter(b)
            updateDeferred(_.deferMatcher(currentGeneration + 1, sb, m.substitute(substituter, msubst)))
          }

          substBlocker
      }

      if (bs != Set(substBlocker)) {
        val (blocker, blockerClauses) = encodeBlockers(bs)
        registerImplication(blocker, substBlocker)
        clauses ++= blockerClauses
        clauses ++= enables(blocker, substBlocker)
      }

      clauses.toSeq
    }

    /** Whether the body matches on function calls or lambdas, whose evaluation unfolds them. */
    def hasComplexMatchers(modelEq: (Encoded, Encoded) => Boolean): Boolean = constraints.exists {
      case (_, _: LambdaKey, _) => true
      case (_, _: FunctionKey, _) => true
      case (_, CallerKey(caller, tt), _) =>
        lambdaTemplates(tt).exists(t => modelEq(t.ids._2, caller))
      case _ => false
    }

    def checkForall(modelEq: (Encoded, Encoded) => Boolean): Option[String] = {
      val quantified = quantifiers.map(_._1).toSet

      if (hasComplexMatchers(modelEq)) return Some("Can't guarantee model for complex matchers.")

      val matchers = exprOps.collect[(Expr, Seq[Expr])] {
        case QuantificationMatcher(e, args) => Set(e -> args)
        case _ => Set.empty
      } (body)

      if (matchers.isEmpty)
        return Some("No matchers found.")

      val matcherToQuants = matchers.foldLeft(Map.empty[Expr, Set[Variable]]) {
        case (acc, (m, args)) => acc + (m -> (acc.getOrElse(m, Set.empty) ++ args.flatMap {
          case v: Variable if quantified(v) => Set(v)
          case _ => Set.empty[Variable]
        }))
      }

      def quantifiedArg(e: Expr): Boolean = e match {
        case v: Variable => quantified(v)
        case QuantificationMatcher(_, args) => args.forall(quantifiedArg)
        case _ => false
      }

      val err = boundary[Option[String]] {
        exprOps.postTraversal(m => m match {
          case QuantificationMatcher(_, args) => // OK

          case Operator(es, _) if es.collect { case v: Variable if quantified(v) => v }.nonEmpty =>
            break[Option[String]](Some("Invalid operation on quantifiers " + m.asString))

          case (_: Equals) | (_: And) | (_: Or) | (_: Implies) | (_: Not) => // OK

          case Operator(es, _) if (es.flatMap(exprOps.variablesOf).toSet & quantified).nonEmpty =>
            break[Option[String]](Some("Unhandled implications from operation " + m.asString))

          case _ => // OK
        })(body)
        Option.empty[String]
      }

      err.orElse(body match {
        case v: Variable if quantified(v) =>
          Some("Unexpected free quantifier " + v.asString)
        case _ => None
      })
    }
  }

  def instantiateQuantification(template: QuantificationTemplate): (Map[Encoded, Encoded], Clauses) = {
    templates.get(template.structure).orElse {
      templates.collectFirst { case (s, t) if s `subsumes` template.structure => t }
    }.map { case (tmpl, inst) =>
      template.polarity match {
        case Positive(subst) =>
          (Map.empty[Encoded, Encoded], Rule.Holds(template.contents.pathVar._2, inst).clauses)
        case Negative(insts) =>
          (Map(insts._2 -> inst), Seq.empty[Encoded])
      }
    }.getOrElse {
      reporter.debug("instantiating quantification " + template.body.asString)

      val newTemplate = template.concretize
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      clauses ++= newTemplate.structure.instantiation

      // explicit map type will raise a warning due ot erasure
      val subst: (Encoded, Map[Encoded, Encoded]) = (newTemplate.polarity match {
        case Positive(subst) =>
          val axiom = new Axiom(newTemplate.contents, subst, newTemplate.body, newTemplate.calleeMatchers, newTemplate.isDeferred)
          state.update(s => s.copy(axioms = s.axioms :+ axiom))

          // the blockers of the matchers now guard instances, so they must hold where enabled
          for ((blocker, matcherBlocker) <- state.get.waitingMatchers) {
            clauses ++= enables(blocker, matcherBlocker)
          }
          state.update(s => s.copy(waitingMatchers = Vector.empty))

          for ((m,b) <- matcherBlockers.toList) {
            clauses ++= axiom.instantiate(b, m)
          }

          updateDeferred(_.deferGrounds(currentGeneration + 3, axiom))
          (trueT, Map.empty)

        case Negative(insts) =>
          val instT = encodeSymbol(insts._1)
          val freshQuants = newTemplate.quantifiers.map(p => encodeSymbol(p._1))
          val substMap = ((newTemplate.quantifiers.map(_._2) :+ insts._2) zip (freshQuants :+ instT).map(Left(_))).toMap
          // this will call `instantiateMatcher` on all matchers in `newTemplate.matchers`
          clauses ++= Rule.Instance(newTemplate.contents.instantiation(newTemplate.contents.pathVar._2, substMap), InstanceOf.Counterexample).clauses

          (instT, Map(insts._2 -> instT))
      })

      val (inst, mapping) = subst

      clauses ++= templates.flatMap { case (key, (tmpl, tinst)) =>
        if (typeOps.simplify(newTemplate.structure.body) == typeOps.simplify(tmpl.structure.body)) {
          val (blocker, cls) = encodeBlockers(Set(newTemplate.contents.pathVar._2, tmpl.contents.pathVar._2))
          val eqConds = (newTemplate.structure.locals zip tmpl.structure.locals)
            .filter(p => p._1 != p._2)
            .map { case ((v, e1), (_, e2)) =>
              val (equality, equalityClauses) = guardedEquality(blocker, v.getType, e1, e2)
              clauses ++= equalityClauses
              equality
            }
          cls ++ Rule.Congruence(blocker +: eqConds, mkEquals(inst, tinst)).clauses
        } else {
          Seq.empty[Encoded]
        }
      }

      state.update(s => s.copy(templates = s.templates.updated(newTemplate.structure, (newTemplate, inst))))
      (mapping, clauses.toSeq)
    }
  }

  protected def promoteQuantifications: Unit = {
    val optGen = quantificationsManager.unrollGeneration
    if (optGen.isEmpty)
      throw new InternalSolverError("Attempting to promote inexistent quantifiers")

    updateDeferred(_.advance((currentGeneration - optGen.get) max 0))
  }

  protected def requiresFiniteRangeCheck: Boolean = !deferred.isEmpty

  /** The clauses that hold when the deferred instantiations add nothing to the model: each deferred
    * matcher and substitution is equal to one that was instantiated. */
  protected def getFiniteRangeClauses: Clauses =
    groundsRangeClauses ++ matchersRangeClauses ++ substsRangeClauses

  /** The axioms whose quantifiers may have no ground can't be checked yet: they make the check
    * fail, and their grounds are due at the current generation. */
  private def groundsRangeClauses: Clauses =
    for ((gen, qs) <- deferred.grounds.toList if qs.exists(!_.hasAllGrounds)) yield {
      updateDeferred(_.postponeGrounds(gen, qs))
      falseT
    }

  /** Each deferred matcher has the arguments of an instantiated matcher of its key. */
  private def matchersRangeClauses: Clauses = {
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]
    val keyClause = MutableMap.empty[MatcherKey, (Clauses, Encoded)]

    for ((_, bs, m) <- deferred.matchers) {
      val key = matcherKey(m)
      val argTypes = key match {
        case tk: TypedKey => matcherArgumentTypes(tk.tpe)._1
        case FunctionKey(tfd) => tfd.params.map(_.getType)
      }

      val (values, clause) = keyClause.getOrElse(key, {
        val insts = matcherBlockers.toList.filter(p => correspond(matcherKey(p._1), key).isDefined)

        val guard = Variable.fresh("guard", BooleanType(), true)
        val elems = argTypes.map(tpe => Variable.fresh("elem", tpe, true))
        val values = argTypes.map(tpe => Variable.fresh("value", tpe, true))
        val expr = andJoin(guard +: (elems zip values).map(p => Equals(p._1, p._2)))

        val guardP = guard -> encodeSymbol(guard)
        val elemsP = elems.map(e => e -> encodeSymbol(e))
        val valuesP = values.map(v => v -> encodeSymbol(v))
        val exprT = mkEncoder(elemsP.toMap ++ valuesP + guardP)(expr)

        val disjuncts = insts.map { case (im, b) =>
          val cond = (m.key, im.key) match {
            case (Left((mcaller, _)), Left((imcaller, _))) if mcaller != imcaller =>
              Some(mkEquals(mcaller, imcaller))
            case _ => None
          }

          val bp = encodeEnablers(Set(b) ++ cond)
          val subst = (elemsP.map(_._2) zip im.args.map(_.encoded)).toMap + (guardP._2 -> bp)
          mkSubstituter(subst)(exprT)
        }

        val res = (valuesP.map(_._2), if (disjuncts.isEmpty) falseT else mkOr(disjuncts*))
        keyClause += key -> res
        res
      })

      val b = encodeEnablers(bs)
      val substMap = (values zip m.args.map(_.encoded)).toMap
      clauses += mkSubstituter(substMap)(mkImplies(b, clause))
    }

    clauses.toSeq
  }

  /** Each deferred substitution of an axiom binds the values of an instantiated one. */
  private def substsRangeClauses: Clauses = {
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]

    for (q <- axioms if deferred.hasSubsts(q)) {
      val guard = Variable.fresh("guard", BooleanType(), true)
      val elems = q.quantifiers.map(_._1)
      val values = elems.map(v => v.freshen)
      val expr = andJoin(guard +: (elems zip values).map(p => Equals(p._1, p._2)))

      val guardP = guard -> encodeSymbol(guard)
      val elemsP = elems.map(e => e -> encodeSymbol(e))
      val valuesP = values.map(v => v -> encodeSymbol(v))
      val exprT = mkEncoder(elemsP.toMap ++ valuesP + guardP)(expr)

      val disjunction = substBlockers.toSeq.collect { case ((sq, subst), b) if q == sq => (b, subst) } match {
        case Seq() => falseT
        case seq => mkOr(seq.map { case (b, subst) =>
          val substMap = (elemsP.map(_._2) zip q.quantifiers.map(p => subst(p._2).encoded)).toMap + (guardP._2 -> b)
          mkSubstituter(substMap)(exprT)
        }*)
      }

      // The clause of a deferred substitution only depends on the values it binds, so the
      // substitutions that bind the same values share one clause, enabled by any of their
      // enablers. Each clause copies the disjunction, and many deferred substitutions bind the
      // same values: in ForallAssoc, 155k of them bind only 11k distinct value tuples.
      val enablersByValues = scala.collection.mutable.LinkedHashMap.empty[Seq[Encoded], List[Set[Encoded]]]
      for ((_, enablers, subst) <- deferred.substsOf(q)) {
        val args = q.quantifiers.map(p => subst(p._2).encoded)
        enablersByValues(args) = enablers :: enablersByValues.getOrElse(args, Nil)
      }

      for ((args, enablerSets) <- enablersByValues) {
        val b = if (enablerSets.exists(_.isEmpty)) trueT else {
          mkOr(enablerSets.reverse.map(enablers => mkAnd(enablers.toSeq*))*)
        }
        val substMap = (valuesP.map(_._2) zip args).toMap
        clauses += mkSubstituter(substMap)(mkImplies(b, disjunction))
      }
    }

    clauses.toSeq
  }

  /** The applications of functions of type `tpe` that the unfolding has instantiated, as their
    * blocker, caller and arguments. */
  protected def getApplications(tpe: FunctionType): Seq[(Encoded, Encoded, Seq[Encoded])] =
    matcherBlockers.toList.collect { case (m @ Matcher(Left((caller, `tpe`)), _, _), b) =>
      (b, caller, m.args.map(_.encoded))
    }

  protected def getGroundInstantiations(e: Encoded, tpe: Type): Seq[(Encoded, Seq[Encoded])] = {
    matcherBlockers.toList.flatMap { case (m, b) =>
      val optArgs = matcherKey(m) match {
        case tp: TypedKey if tpe == tp.tpe => Some(m.args.map(_.encoded))
        case _ => None
      }

      optArgs.map(args => b -> args)
    }
  }
}
