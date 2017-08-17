/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import evaluators._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, Queue}

trait QuantificationTemplates { self: Templates =>
  import program._
  import program.trees._
  import program.symbols._

  import lambdasManager._
  import quantificationsManager._

  /* -- Extraction helpers -- */

  object QuantificationMatcher {
    private def flatApplication(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case Application(fi: FunctionInvocation, args) => None
      case Application(caller: Application, args) => flatApplication(caller) match {
        case Some((c, prevArgs)) => Some((c, prevArgs ++ args))
        case None => None
      }
      case Application(caller, args) => Some((caller, args))
      case _ => None
    }

    def unapply(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case IsTyped(a: Application, ft: FunctionType) => None
      case Application(e, args) => flatApplication(expr)
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
    private def flatApplication(expr: Expr): Option[(TypedFunDef, Seq[Expr])] = expr match {
      case Application(fi: FunctionInvocation, args) => Some((fi.tfd, args))
      case Application(caller: Application, args) => flatApplication(caller) match {
        case Some((c, prevArgs)) => Some((c, prevArgs ++ args))
        case None => None
      }
      case _ => None
    }

    def unapply(expr: Expr): Option[(TypedFunDef, Seq[Expr])] = expr match {
      case IsTyped(a: Application, ft: FunctionType) => None
      case Application(e, args) => flatApplication(expr)
      case fi @ FunctionInvocation(_, _, args) => Some((fi.tfd, args))
      case _ => None
    }
  }

  object QuantificationTypeMatcher {
    private def flatType(tpe: Type): (Seq[Type], Type) = tpe match {
      case FunctionType(from, to) =>
        val (nextArgs, finalTo) = flatType(to)
        (from ++ nextArgs, finalTo)
      case _ => (Seq.empty, tpe)
    }

    def unapply(tpe: Type): Option[(Seq[Type], Type)] = tpe match {
      case FunctionType(from, to) => Some(flatType(tpe))
      case MapType(from, to) => Some(Seq(from) -> to)
      case BagType(base) => Some(Seq(base) -> IntegerType)
      case SetType(base) => Some(Seq(base) -> BooleanType)
      case _ => None
    }
  }

  /* -- Quantifier template definitions -- */

  /** Represents the polarity of the quantification within the considered
    * formula. Positive and negative polarity enable optimizations during
    * quantifier instantiation.
    *
    * Unknown polarity is treated conservatively (subsumes both positive and
    * negative cases).
    */
  sealed abstract class Polarity {
    def substitute(substituter: Encoded => Encoded): Polarity = this match {
      case Positive(guard) => Positive(guard)
      case Negative(insts) => Negative(insts._1 -> substituter(insts._2))
      case Unknown(qs, q2s, insts, guard) => Unknown(qs._1 -> substituter(qs._2), q2s, insts, guard)
    }
  }

  case class Positive(guard: Encoded) extends Polarity
  case class Negative(insts: (Variable, Encoded)) extends Polarity

  /** Unknown quantification polarity.
    *
    * Instantiations of unknown polarity quantification with body {{{p}}} follows the schema:
    * {{{
    *    q == (q2 && inst)
    *    inst == (guard ==> p)
    * }}}
    * It is useful to keep the two clauses separate so that satisfying assignments can be
    * constructed where only certain `inst` variables are falsified. This is used to enable
    * a powerful unrolling heuristic in the presence of both quantifiers and recursive functions.
    */
  case class Unknown(qs: (Variable, Encoded), q2s: (Variable, Encoded), insts: (Variable, Encoded), guard: Encoded) extends Polarity

  class QuantificationTemplate private[QuantificationTemplates] (
    val polarity: Polarity,
    val contents: TemplateContents,
    val structure: TemplateStructure,
    val body: Expr,
    stringRepr: () => String,
    private val isConcrete: Boolean) {

    lazy val quantifiers = contents.arguments

    lazy val start = contents.pathVar._2
    lazy val mapping: Map[Variable, Encoded] = polarity match {
      case Positive(_) => Map.empty
      case Negative(insts) => Map(insts)
      case Unknown(qs, _, _, _) => Map(qs)
    }

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]) =
      new QuantificationTemplate(
        polarity.substitute(substituter),
        contents.substitute(substituter, msubst),
        structure.substitute(substituter, msubst),
        body, stringRepr, isConcrete
      )

    def concretize: QuantificationTemplate = {
      assert(!isConcrete, "Can't concretize concrete quantification template")
      val substituter = mkSubstituter(structure.instantiationSubst)
      new QuantificationTemplate(polarity,
        contents.substitute(substituter, Map.empty),
        structure, body, stringRepr, true)
    }

    private lazy val str : String = stringRepr()
    override def toString : String = str
  }

  object QuantificationTemplate {
    def apply(
      pathVar: (Variable, Encoded),
      optPol: Option[Boolean],
      forall: Forall,
      substMap: Map[Variable, Encoded]
    ): (Option[Variable], QuantificationTemplate) = {
      val (Forall(args, body), structure, depSubst) =
        mkExprStructure(pathVar._1, forall, substMap, onlySimple = !simpOpts.simplify)

      val quantifiers = args.map(_.toVariable).toSet
      val idQuantifiers: Seq[Variable] = args.map(_.toVariable)
      val trQuantifiers: Seq[Encoded] = forall.args.map(v => encodeSymbol(v.toVariable))

      val clauseSubst: Map[Variable, Encoded] = depSubst ++ (idQuantifiers zip trQuantifiers)
      val (p, tmplClauses) = mkExprClauses(pathVar._1, body, clauseSubst)

      val (optVar, polarity, extraGuarded, extraEqs, extraSubst): (
        Option[Variable],
        Polarity,
        Map[Variable, Seq[Expr]],
        Seq[Expr],
        Map[Variable, Encoded]
      ) = optPol match {
        case Some(true) =>
          val guard = encodeSymbol(Variable.fresh("guard", BooleanType, true))
          val extraSubst = Map(pathVar._1 -> guard)
          val extraGuarded = Map(pathVar._1 -> Seq(p))
          (None, Positive(guard), extraGuarded, Seq.empty, extraSubst)

        case Some(false) =>
          val inst: Variable = Variable.fresh("inst", BooleanType, true)
          val insts = inst -> encodeSymbol(inst)
          val extraGuarded = Map(pathVar._1 -> Seq(Equals(inst, p)))
          (Some(inst), Negative(insts), extraGuarded, Seq.empty, Map(insts))

        case None =>
          val q: Variable = Variable.fresh("q", BooleanType, true)
          val q2: Variable = Variable.fresh("qo", BooleanType, true)
          val inst: Variable = Variable.fresh("inst", BooleanType, true)
          val guard = encodeSymbol(Variable.fresh("guard", BooleanType, true))

          val qs = q -> encodeSymbol(q)
          val q2s = q2 -> encodeSymbol(q2)
          val insts = inst -> encodeSymbol(inst)

          val polarity = Unknown(qs, q2s, insts, guard)
          val extraEqs = Seq(Equals(q, And(q2, inst)), Equals(inst, Implies(pathVar._1, p)))
          (Some(q), polarity, Map.empty, extraEqs, Map(qs, q2s, insts) + (pathVar._1 -> guard))
      }

      val (conds, exprs, chooses, tree, guarded, eqs, equalities, lambdas, quants) = tmplClauses

      // Note @nv: some hacky shit is going on here...
      // We are overriding the mapping of `pathVar._1` for certain polarities so that
      // the encoded clauses use the `guard` as blocker instead of `pathVar._2`. This only
      // works due to [[Template.encode]] injecting `pathVar` BEFORE `substMap` into the
      // global encoding substitution.
      val (contents, str) = Template.contents(pathVar, idQuantifiers zip trQuantifiers, (
        conds, exprs, chooses, tree, extraGuarded merge guarded, extraEqs ++ eqs, equalities, lambdas, quants
      ), depSubst ++ extraSubst)

      (optVar, new QuantificationTemplate(polarity, contents, structure,
        body, () => "Template for " + forall.asString + " is :\n" + str(), false))
    }
  }

  private[unrolling] object quantificationsManager extends Manager {
    val quantifications = new IncrementalSeq[Quantification]

    private[QuantificationTemplates] val ignoredMatchers = new IncrementalSeq[(Int, Set[Encoded], Matcher)]

    // to avoid [[MatcherSet]] escaping defining context, we must keep this ~private
    private[QuantificationTemplates] val handledMatchers = new MatcherSet

    private[QuantificationTemplates] val ignoredSubsts   = new IncrementalMap[Quantification, Set[(Int, Set[Encoded], Map[Encoded,Arg])]]
    private[QuantificationTemplates] val handledSubsts   = new IncrementalMap[Quantification, Set[(Set[Encoded], Map[Encoded,Arg])]]
    private[QuantificationTemplates] val ignoredGrounds  = new IncrementalMap[Int, Set[Quantification]]

    private[QuantificationTemplates] val lambdaAxioms    = new IncrementalSet[TemplateStructure]
    private[QuantificationTemplates] val templates       = new IncrementalMap[TemplateStructure, (QuantificationTemplate, Encoded)]

    val incrementals: Seq[IncrementalState] = Seq(quantifications, lambdaAxioms, templates,
      ignoredMatchers, handledMatchers, ignoredSubsts, handledSubsts, ignoredGrounds)

    override def push(): Unit  = { super.push();  for (q <- quantifications) q.push()  }
    override def pop(): Unit   = { super.pop();   for (q <- quantifications) q.pop()   }
    override def clear(): Unit = { super.clear(); for (q <- quantifications) q.clear() }
    override def reset(): Unit = { super.reset(); for (q <- quantifications) q.reset() }

    private def assumptions: Seq[Encoded] =
      quantifications.collect { case q: GeneralQuantification => q.currentQ2Var }

    def satisfactionAssumptions = assumptions
    def refutationAssumptions = assumptions

    def unrollGeneration: Option[Int] = {
      val gens: Seq[Int] = ignoredMatchers.toSeq.map(_._1) ++
        ignoredSubsts.flatMap(p => p._2.map(_._1)) ++
        ignoredGrounds.map(_._1)
      if (gens.isEmpty) None else Some(gens.min)
    }

    // promoting blockers makes no sense in this context
    def promoteBlocker(b: Encoded): Boolean = false

    def unroll: Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      for (e @ (gen, bs, m) <- ignoredMatchers.toList if gen <= currentGeneration && !abort && !pause) {
        clauses ++= instantiateMatcher(bs, m, defer = true)
        ignoredMatchers -= e
      }

      ctx.reporter.debug("Unrolling ignored matchers (" + clauses.size + ")")
      for (cl <- clauses) {
        ctx.reporter.debug("  . " + cl)
      }

      if (abort || pause) return clauses.toSeq

      val suClauses = new scala.collection.mutable.ListBuffer[Encoded]
      for (q <- quantifications.toSeq if ignoredSubsts.isDefinedAt(q) && !abort && !pause) {
        val (release, keep) = ignoredSubsts(q).partition(_._1 <= currentGeneration)
        ignoredSubsts += q -> keep

        for ((_, bs, subst) <- release) {
          suClauses ++= q.instantiateSubst(bs, subst, defer = true)
        }
      }

      ctx.reporter.debug("Unrolling ignored substitutions (" + suClauses.size + ")")
      for (cl <- suClauses) {
        ctx.reporter.debug("  . " + cl)
      }

      clauses ++= suClauses

      if (abort || pause) return clauses.toSeq

      val grClauses = new scala.collection.mutable.ListBuffer[Encoded]
      for ((gen, qs) <- ignoredGrounds.toList if gen <= currentGeneration && !abort && !pause; q <- qs if !abort) {
        grClauses ++= q.ensureGrounds
        val remaining = ignoredGrounds.getOrElse(gen, Set.empty) - q
        if (remaining.nonEmpty) {
          ignoredGrounds += gen -> remaining
        } else {
          ignoredGrounds -= gen
        }
      }

      ctx.reporter.debug("Unrolling ignored grounds (" + grClauses.size + ")")
      for (cl <- grClauses) {
        ctx.reporter.debug("  . " + cl)
      }

      clauses ++= grClauses

      clauses.toSeq
    }
  }

  def instantiateMatcher(blocker: Encoded, matcher: Matcher): Clauses = {
    // first instantiate sub-matchers
    val subs = matcher.args.collect { case Right(m) =>
      instantiateMatcher(Set(blocker), m, false)
    }.flatten

    subs ++ instantiateMatcher(Set(blocker), matcher, false)
  }

  @inline
  private def instantiateMatcher(blockers: Set[Encoded], matcher: Matcher, defer: Boolean = false): Clauses = {
    val relevantBlockers = blockerPath(blockers)

    if (handledMatchers(relevantBlockers -> matcher)) {
      Seq.empty
    } else if (abort || pause) {
      ignoredMatchers += ((currentGeneration, blockers, matcher))
      Seq.empty
    } else {
      ctx.reporter.debug(" -> instantiating matcher " + blockers.mkString("{",",","}") + " ==> " + matcher)
      handledMatchers += relevantBlockers -> matcher
      val qClauses: Clauses = quantifications.flatMap(_.instantiate(relevantBlockers, matcher, defer))

      val mClauses: Clauses = matcherKey(matcher) match {
        /* XXX @nv: this is actually unsound. Consider
         * {{{
         * def id(a: A): A = a
         * case class A(i: Int) { require(id(this).i >= 0) }
         * }}}
         * We would assume `this.i >= 0` while trying to prove it!
         *
        case FunctionKey(tfd) =>
          val (b, encClauses) = encodeBlockers(relevantBlockers)
          encClauses ++ unrollInvariant(b, matcher.encoded, tfd.returnType)
        case TypeKey(MapType(_, to)) =>
          val (b, encClauses) = encodeBlockers(relevantBlockers)
          encClauses ++ unrollInvariant(b, matcher.encoded, to)
         */
        case _ => Seq.empty
      }

      qClauses ++ mClauses
    }
  }

  def hasQuantifiers: Boolean = quantifications.nonEmpty

  def getQuantifications: Seq[Quantification] = quantifications.toSeq

  def getInstantiationsWithBlockers = quantifications.toSeq.flatMap {
    case q: GeneralQuantification => q.instantiations.toSeq
    case _ => Seq.empty
  }

  private sealed trait MatcherKey
  private case class FunctionKey(tfd: TypedFunDef) extends MatcherKey
  private sealed abstract class TypedKey(val tpe: Type) extends MatcherKey
  private case class LambdaKey(lambda: Lambda, tt: Type) extends TypedKey(tt)
  private case class CallerKey(caller: Encoded, tt: FunctionType) extends TypedKey(tt)
  private case class TypeKey(tt: Type) extends TypedKey(tt)

  private def matcherKey(key: Either[(Encoded, Type), TypedFunDef]): MatcherKey = key match {
    case Right(tfd) =>
      FunctionKey(tfd)
    case Left((caller, ft: FunctionType)) if byID.isDefinedAt(caller) =>
      LambdaKey(byID(caller).structure.body.asInstanceOf[Lambda], ft)
    case Left((caller, ft: FunctionType)) =>
      CallerKey(caller, ft)
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

  @inline
  protected def correspond(m1: Matcher, m2: Matcher): Option[Boolean] =
    correspond(matcherKey(m1), matcherKey(m2))

  private trait BlockedSet[Element] extends Iterable[(Set[Encoded], Element)] with IncrementalState {
    private var map: MutableMap[Any, (Element, MutableSet[Set[Encoded]])] = MutableMap.empty
    private var stack: List[MutableMap[Any, (Element, MutableSet[Set[Encoded]])]] = List.empty

    /** Override point to determine the "key" associated to element [[e]].
      *
      * By default, simply returns the given element. */
    protected def key(e: Element): Any = e

    /** Override point to merge two elements [[e1]] and [[e2]] that share the same key.
      *
      * By default, simply returns the first element [[e1]]. Note that this is consistent
      * with the default implementation of the [[key]] method since
      * {{{key(e1) == key(e2)}}} iff {{{e1 == e2}}}.
      *
      * @see [[key]] for element key extraction
      */
    protected def merge(e1: Element, e2: Element): Element = e1

    protected def contained(s: Set[Encoded], ss: Set[Encoded] => Boolean): Boolean = ss(s) || {
      // we assume here that iterating through the powerset of `s`
      // will be significantly faster then iterating through `ss`
      s.subsets.exists(set => ss(set))
    }

    @inline
    protected def get(k: Any): Option[Set[Encoded] => Boolean] = map.get(k).map(_._2)

    def apply(p: (Set[Encoded], Element)): Boolean = get(key(p._2)).exists {
      blockerSets => contained(p._1, blockerSets)
    }

    def +=(p: (Set[Encoded], Element)): Unit = {
      val k = key(p._2)
      val (elem, blockerSets) = map.get(k) match {
        case Some((elem, blockerSets)) =>
          (merge(p._2, elem), blockerSets)
        case None =>
          (p._2, MutableSet.empty[Set[Encoded]])
      }

      if (!contained(p._1, blockerSets)) {
        blockerSets += p._1
      }

      map(k) = (elem, blockerSets)
    }

    def iterator: Iterator[(Set[Encoded], Element)] = new collection.AbstractIterator[(Set[Encoded], Element)] {
      private val mapIt: Iterator[(Any, (Element, MutableSet[Set[Encoded]]))] = BlockedSet.this.map.iterator
      private var setIt: Iterator[Set[Encoded]] = Iterator.empty
      private var current: Element = _

      def hasNext = mapIt.hasNext || setIt.hasNext
      def next: (Set[Encoded], Element) = if (setIt.hasNext) {
        val bs = setIt.next
        bs -> current
      } else {
        val (_, (e, bss)) = mapIt.next
        current = e
        setIt = bss.iterator
        next
      }
    }

    def push(): Unit = {
      val newMap: MutableMap[Any, (Element, MutableSet[Set[Encoded]])] = MutableMap.empty
      for ((k, (e, bss)) <- map) {
        newMap += k -> (e -> bss.clone)
      }
      stack ::= map
      map = newMap
    }

    def pop(): Unit = {
      val (head :: tail) = stack
      map = head
      stack = tail
    }

    def clear(): Unit = {
      stack = List.empty
      map = MutableMap.empty
    }

    def reset(): Unit = clear()
  }

  /** Ground instantiations are annotated with an {{{Set[Int]}}} value that specifies
    * the (optional) abstract generations at which this instantiation was added to the set.
    * The abstract generations exist iff the matchers do not exactly correspond (for example,
    * abstract matcher {{{f(x)}}} instantiated against concrete application {{{g(1)}}}).
    *
    * Instantiating {{{f(x)}}} against {{{f(1)}}} will lead to an EMPTY abstract generation set.
    *
    * If we see an {{{f(1)}}} instantiation and had some abstract instantiation corresponding
    * to {{{g(1)}}} in our set of instantiations, we can forget about {{{g(1)}}} as {{{f(1)}}}
    * is "more certain". If we see {{{h(1)}}} and had {{{g(1)}}}, we can merge the two sets.
    */
  private class GroundSet extends BlockedSet[(Arg, Set[Int])] {
    override protected def key(ag: (Arg, Set[Int])) = ag._1
    override protected def merge(ag1: (Arg, Set[Int]), ag2: (Arg, Set[Int])): (Arg, Set[Int]) = {
      if (ag1._2.isEmpty || ag2._2.isEmpty) (ag1._1 -> Set.empty)
      else (ag1._1 -> (ag1._2 ++ ag2._2))
    }

    def apply(bs: Set[Encoded], arg: Arg): Boolean = get(arg).exists {
      blockerSets => contained(bs, blockerSets)
    }

    @inline
    def +=(p: (Set[Encoded], Arg, Set[Int])): Unit = this += (p._1 -> (p._2 -> p._3))

    def unzipSet: Set[(Set[Encoded], Arg, Set[Int])] = iterator.map(p => (p._1, p._2._1, p._2._2)).toSet
  }

  private class MatcherSet extends BlockedSet[Matcher] {
    private val keys = new IncrementalSet[(MatcherKey, Seq[Arg])]
    def contains(m: Matcher): Boolean = keys(matcherKey(m) -> m.args)
    def containsAll(ms: Set[Matcher]): Boolean = ms.forall(contains)

    override def +=(p: (Set[Encoded], Matcher)): Unit = {
      keys += matcherKey(p._2) -> p._2.args
      super.+=(p)
    }

    override def push(): Unit = { keys.push(); super.push() }
    override def pop(): Unit  = { keys.pop();  super.pop()  }
    override def clear(): Unit = { keys.clear(); super.clear() }
    override def reset(): Unit = { keys.reset(); super.reset() }
  }

  private def totalDepth(m: Matcher): Int = 1 + m.args.map {
    case Right(ma) => totalDepth(ma)
    case _ => 0
  }.sum

  private def encodeEnablers(es: Set[Encoded]): Encoded =
    if (es.isEmpty) trueT else mkAnd(es.toSeq.sortBy(_.toString) : _*)

  private[solvers] trait Quantification extends IncrementalState {
    val guard: Encoded
    val contents: TemplateContents

    val holds: Encoded
    val body: Expr

    def getPolarity: Option[Boolean]

    lazy val quantifiers = contents.arguments
    lazy val quantified: Set[Encoded] = quantifiers.map(_._2).toSet
    lazy val pathBlockers = blockerPath(contents.pathVar._2)

    private val constraints: Seq[(Encoded, MatcherKey, Int)] = (for {
      (_, ms) <- contents.matchers
      m <- ms
      (arg,i) <- m.args.zipWithIndex
      q <- arg.left.toOption if quantified(q)
    } yield (q, matcherKey(m), i)).toSeq

    private val groupedConstraints: Map[Encoded, Seq[(MatcherKey, Int)]] =
      constraints.groupBy(_._1).map(p => p._1 -> p._2.map(p2 => (p2._2, p2._3)))

    private val grounds: Map[Encoded, GroundSet] = quantified.map(q => q -> new GroundSet).toMap

    private var generationCounter: Int = 0

    def push(): Unit = for (gs <- grounds.values) gs.push()
    def pop(): Unit = for (gs <- grounds.values) gs.pop()
    def clear(): Unit = for (gs <- grounds.values) gs.clear()
    def reset(): Unit = for (gs <- grounds.values) gs.reset()

    private val optimizationQuorums: Seq[Set[Matcher]] = {
      def matchersOf(m: Matcher): Set[Matcher] = m.args.flatMap {
        case Right(m) => matchersOf(m) + m
        case _ => Set.empty[Matcher]
      }.toSet

      def quantifiersOf(m: Matcher): Set[Encoded] =
        (matchersOf(m) + m).flatMap(_.args.collect { case Left(q) if quantified(q) => q })

      val allMatchers = contents.matchers.flatMap(_._2).toList
      val allQuorums = allMatchers.toSet.subsets
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

    def instantiate(bs: Set[Encoded], m: Matcher, defer: Boolean = false): Clauses = {

      generationCounter += 1
      val gen = generationCounter

      /* Build mappings from quantifiers to all potential ground values previously encountered. */
      val quantToGround: Map[Encoded, Set[(Set[Encoded], Arg, Set[Int])]] =
        for ((q, constraints) <- groupedConstraints) yield q -> {
          grounds(q).unzipSet ++ constraints.flatMap {
            case (key, i) => correspond(matcherKey(m), key).map {
              p => (bs, m.args(i), if (p) Set.empty[Int] else Set(gen))
            }
          }
        }

      /* Transform the map to sets into a sequence of maps making sure that the current
       * matcher is part of the mapping (otherwise, instantiation has already taken place). */
      var mappings: Seq[(Set[Encoded], Map[Encoded, Arg], Int)] = Seq.empty
      for ((q, constraints) <- groupedConstraints;
           (key, i) <- constraints;
           perfect <- correspond(matcherKey(m), key)) {
        val initGens: Set[Int] = if (perfect && !defer) Set.empty else Set(gen)
        val newMappings = (quantified - q).foldLeft(Seq((bs, Map(q -> m.args(i)), initGens, 0))) {
          case (maps, oq) => for {
            (bs, map, gens, c) <- maps
            groundSet <- quantToGround.get(oq).toSeq
            (ibs, inst, igens) <- groundSet
          } yield {
            val delay = if (igens.isEmpty || (gens intersect igens).nonEmpty) 0 else 1
            (bs ++ ibs, map + (oq -> inst), gens ++ igens, c + delay)
          }
        }

        /* @nv: I reused the cost heuristic from Leon here, it worked pretty well
         *      on all our pre-existing benchmarks and regressions. */
        mappings ++= newMappings.map { case (bs, map, gens, c) =>
          val cost = if (initGens.nonEmpty) {
            1 + 3 * map.values.collect { case Right(m) => totalDepth(m) }.sum
          } else {
            val substituter = mkSubstituter(map.mapValues(_.encoded))
            val msubst = map.collect { case (q, Right(m)) => q -> m }
            val opts = optimizationQuorums.flatMap { ms =>
              val sms = ms.map(_.substitute(substituter, msubst))
              if (handledMatchers.containsAll(sms)) sms.toList else Nil
            }

            if (opts.nonEmpty) {
              val tms = contents.matchers.flatMap(_._2.map(_.substitute(substituter, msubst)))
              if (opts.map(totalDepth).max >= tms.map(totalDepth).max) 0
              else 3
            } else if (grounds(q)(bs, m.args(i))) {
              10
            } else {
              3
            }
          }

          (bs, map, c + cost)
        }

        // register ground instantiation for future instantiations
        grounds(q) += ((bs, m.args(i), initGens))
      }

      instantiateSubsts(mappings)
    }

    def hasAllGrounds: Boolean = quantified.forall(q => grounds(q).nonEmpty)

    def ensureGrounds: Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]

      /* Build mappings from quantifiers to all potential ground values previously encountered
       * AND the constants we're introducing to make sure grounds are non-empty. */
      val quantToGround = (for ((v,q) <- quantifiers) yield {
        val groundsSet: Set[(Set[Encoded], Arg, Set[Int])] = grounds(q).unzipSet
        val newGrounds: Set[(Set[Encoded], Arg, Set[Int])] = {
          if (groundsSet.isEmpty) {
            clauses ++= registerSymbol(contents.pathVar._2, q, v.tpe)
            Set((Set(), Left(q), Set()))
          } else {
            Set.empty
          }
        }

        q -> (groundsSet ++ newGrounds)
      }).toMap

      /* Generate the sequence of all relevant instantiation mappings */
      var mappings: Seq[(Set[Encoded], Map[Encoded, Arg], Int)] = Seq.empty
      for (q <- quantified if grounds(q).isEmpty) {
        val init: Seq[(Set[Encoded], Map[Encoded, Arg], Set[Int], Int)] = Seq((Set(), Map(q -> Left(q)), Set(), 0))
        val newMappings = (quantified - q).foldLeft(init) { case (maps, oq) =>
          for ((bs, map, gens, c) <- maps; (ibs, inst, igens) <- quantToGround(oq)) yield {
            val delay = if (igens.isEmpty || (gens intersect igens).nonEmpty) 0 else 1
            (bs ++ ibs, map + (oq -> inst), gens ++ igens, c + delay)
          }
        }

        mappings ++= newMappings.map { case (bs, map, gens, c) =>
          (bs, map, c + (3 * map.values.collect { case Right(m) => totalDepth(m) }.sum))
        }

        grounds(q) += ((Set.empty[Encoded], Left(q), Set.empty[Int]))
      }

      clauses ++= instantiateSubsts(mappings)
      clauses.toSeq
    }

    private def instantiateSubsts(substs: Seq[(Set[Encoded], Map[Encoded, Arg], Int)]): Clauses = {
      val instantiation = new scala.collection.mutable.ListBuffer[Encoded]

      for (p @ (bs, subst, delay) <- substs if !handledSubsts.get(this).exists(_ contains (bs -> subst))) {
        if (abort || pause || delay > 0) {
          val gen = currentGeneration + delay + (if (getPolarity.isEmpty) 2 else 0)
          ignoredSubsts += this -> (ignoredSubsts.getOrElse(this, Set.empty) + ((gen, bs, subst)))
        } else {
          instantiation ++= instantiateSubst(bs, subst, defer = false)
        }
      }

      instantiation.toSeq
    }

    def instantiateSubst(bs: Set[Encoded], subst: Map[Encoded, Arg], defer: Boolean = false): Clauses = {
      handledSubsts += this -> (handledSubsts.getOrElse(this, Set.empty) + (bs -> subst))
      val instantiation = new scala.collection.mutable.ListBuffer[Encoded]

      val (enabler, enablerClauses) = encodeBlockers(bs ++ pathBlockers)
      instantiation ++= enablerClauses

      val baseSubst = subst ++ instanceSubst(enabler).mapValues(Left(_))
      val (substClauses, substMap) = contents.substitution(enabler, baseSubst)
      instantiation ++= substClauses

      val msubst = substMap.collect { case (c, Right(m)) => c -> m }
      val substituter = mkSubstituter(substMap.mapValues(_.encoded))
      registerBlockers(substituter)

      // matcher instantiation must be manually controlled here to avoid never-ending loops
      instantiation ++= Template.instantiate(
        contents.clauses, contents.blockers, contents.applications,
        Map.empty, contents.equalities, substMap)

      for ((b,ms) <- contents.matchers; m <- ms) {
        val sb = bs ++ (if (b == guard) Set.empty else Set(substituter(b)))
        val sm = m.substitute(substituter, msubst)

        if (abort || pause || b != guard) {
          val gen = currentGeneration + 1
          ignoredMatchers += ((gen, sb, sm))
        } else {
          instantiation ++= instantiateMatcher(sb, sm, defer = defer)
        }
      }

      for (tmpl <- contents.lambdas.map(t => byID(substituter(t.ids._2)))) {
        instantiation ++= instantiateAxiom(tmpl)
      }

      for ((_, apps) <- contents.applications;
           App(caller, _, _, _) <- apps; tmpl <- byID.get(substituter(caller))) {
        instantiation ++= instantiateAxiom(tmpl)
      }

      instantiation.toSeq
    }

    protected def instanceSubst(enabler: Encoded): Map[Encoded, Encoded]

    protected def registerBlockers(substituter: Encoded => Encoded): Unit = ()

    def checkForall(modelEq: (Encoded, Encoded) => Boolean): Option[String] = {
      val quantified = quantifiers.map(_._1).toSet

      if (constraints.exists {
        case (_, _: LambdaKey, _) => true
        case (_, _: FunctionKey, _) => true
        case (_, CallerKey(caller, tt), _) =>
          byType(tt).values.exists(t => modelEq(t.ids._2, caller))
        case _ => false
      }) return Some("Can't guarantee model for complex matchers.")

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

      exprOps.postTraversal(m => m match {
        case QuantificationMatcher(_, args) => // OK

        case Operator(es, _) if es.collect { case v: Variable if quantified(v) => v }.nonEmpty =>
          return Some("Invalid operation on quantifiers " + m.asString)

        case (_: Equals) | (_: And) | (_: Or) | (_: Implies) | (_: Not) => // OK

        case Operator(es, _) if (es.flatMap(exprOps.variablesOf).toSet & quantified).nonEmpty =>
          return Some("Unandled implications from operation " + m.asString)

        case _ => // OK
      }) (body)

      body match {
        case v: Variable if quantified(v) =>
          Some("Unexpected free quantifier " + v.asString)
        case _ => None
      }
    }
  }

  private class GeneralQuantification (
    val qs: (Variable, Encoded),
    val q2s: (Variable, Encoded),
    val insts: (Variable, Encoded),
    val guard: Encoded,
    val contents: TemplateContents,
    val body: Expr) extends Quantification {

    private var _currentQ2Var: Encoded = qs._2
    def currentQ2Var = _currentQ2Var
    val holds = qs._2

    def getPolarity = None

    private var _insts: Map[Encoded, Set[Encoded]] = Map.empty
    def instantiations = _insts

    protected def instanceSubst(enabler: Encoded): Map[Encoded, Encoded] = {
      val nextQ2Var = encodeSymbol(q2s._1)

      val subst = Map(qs._2 -> currentQ2Var, guard -> enabler,
        q2s._2 -> nextQ2Var, insts._2 -> encodeSymbol(insts._1))

      _currentQ2Var = nextQ2Var
      subst
    }

    override def registerBlockers(substituter: Encoded => Encoded): Unit = {
      val freshInst = substituter(insts._2)
      val bs = (contents.blockers.keys ++ contents.applications.keys).map(substituter).toSet
      _insts += freshInst -> bs
    }
  }

  private class Axiom (
    val guard: Encoded,
    val contents: TemplateContents,
    val body: Expr) extends Quantification {

    val holds = trueT

    def getPolarity = Some(true)

    protected def instanceSubst(enabler: Encoded): Map[Encoded, Encoded] = {
      Map(guard -> enabler)
    }
  }

  def instantiateAxiom(template: LambdaTemplate): Clauses = {
    if (lambdaAxioms(template.structure) || lambdaAxioms.exists(s => s.subsumes(template.structure))) {
      Seq.empty
    } else {
      lambdaAxioms += template.structure
      val quantifiers = template.contents.arguments
      val app = mkFlatApp(template.ids._2, template.tpe, quantifiers.map(_._2))
      val matcher = Matcher(Left(template.ids._2 -> template.tpe), quantifiers.map(p => Left(p._2)), app)

      val guard = encodeSymbol(Variable.fresh("guard", BooleanType, true))
      val substituter = mkSubstituter(Map(template.start -> guard))

      val body: Expr = {
        def rec(caller: Expr, body: Expr): Expr = body match {
          case Lambda(args, body) => rec(Application(caller, args.map(_.toVariable)), body)
          case _ => Equals(caller, body)
        }
        rec(template.ids._1, template.structure.body)
      }

      instantiateQuantification(new QuantificationTemplate(
        Positive(guard),
        template.contents.substitute(substituter, Map.empty).copy(
          matchers = template.contents.matchers merge Map(guard -> Set(matcher))
        ), template.structure, body, template.stringRepr, false))._2 // mapping is guaranteed empty!!
    }
  }

  def instantiateQuantification(template: QuantificationTemplate): (Map[Encoded, Encoded], Clauses) = {
    templates.get(template.structure).orElse {
      templates.collectFirst { case (s, t) if s subsumes template.structure => t }
    }.map { case (tmpl, inst) =>
      template.polarity match {
        case Positive(guard) =>
          (Map.empty[Encoded, Encoded], Seq(mkImplies(template.contents.pathVar._2, inst)))
        case Negative(insts) =>
          (Map(insts._2 -> inst), Seq.empty[Encoded])
        case Unknown(qs, q2s, insts, guard) =>
          (Map(qs._2 -> inst), Seq.empty[Encoded])
      }
    }.getOrElse {
      ctx.reporter.debug("instantiating quantification " + template.body.asString)

      val newTemplate = template.concretize
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      clauses ++= newTemplate.structure.instantiation

      val (inst, mapping): (Encoded, Map[Encoded, Encoded]) = newTemplate.polarity match {
        case Positive(guard) =>
          val axiom = new Axiom(guard, newTemplate.contents, newTemplate.body)
          quantifications += axiom

          for ((bs,m) <- handledMatchers.toList) {
            clauses ++= axiom.instantiate(bs, m)
          }

          val groundGen = currentGeneration + 3
          ignoredGrounds += groundGen -> (ignoredGrounds.getOrElse(groundGen, Set.empty) + axiom)
          (trueT, Map.empty)

        case Negative(insts) =>
          val instT = encodeSymbol(insts._1)
          val (substClauses, substMap) = newTemplate.contents.substitution(
            newTemplate.contents.pathVar._2,
            Map(insts._2 -> Left(instT))
          )

          clauses ++= substClauses

          val freshQuants = newTemplate.quantifiers.map(p => encodeSymbol(p._1))
          val freshSubst = (newTemplate.quantifiers.map(_._2) zip freshQuants.map(Left(_))).toMap
          val fullSubst = substMap ++ freshSubst

          // this will call `instantiateMatcher` on all matchers in `newTemplate.matchers`
          clauses ++= newTemplate.contents.instantiate(fullSubst)

          for ((v,q) <- newTemplate.quantifiers.map(_._1) zip freshQuants) {
            clauses ++= registerSymbol(newTemplate.contents.pathVar._2, q, v.tpe)
          }

          (instT, Map(insts._2 -> instT))

        case Unknown(qs, q2s, insts, guard) =>
          val qT = encodeSymbol(qs._1)
          val substituter = mkSubstituter(Map(qs._2 -> qT))

          val quantification = new GeneralQuantification(
            qs._1 -> qT, q2s, insts, guard, newTemplate.contents.copy(
              // one clause depends on 'qs._2' (and therefore 'qT')
              clauses = newTemplate.contents.clauses map substituter
            ), newTemplate.body)

          quantifications += quantification

          for ((bs,m) <- handledMatchers.toList) {
            clauses ++= quantification.instantiate(bs, m)
          }

          val freshQuantifiers = newTemplate.quantifiers.map(p => encodeSymbol(p._1))
          val freshSubst = mkSubstituter((newTemplate.quantifiers.map(_._2) zip freshQuantifiers).toMap)
          for ((b,ms) <- newTemplate.contents.matchers; m <- ms) {
            clauses ++= instantiateMatcher(Set.empty[Encoded], m, false)
            // it is very rare that such instantiations are actually required, so we defer them
            val gen = currentGeneration + 20
            ignoredMatchers += ((gen, Set(b), m.substitute(freshSubst, Map.empty)))
          }

          for (((v,_), q) <- newTemplate.quantifiers zip freshQuantifiers) {
            clauses ++= registerSymbol(newTemplate.start, q, v.tpe)
          }

          clauses ++= quantification.ensureGrounds
          (qT, Map(qs._2 -> qT))
      }

      clauses ++= templates.flatMap { case (key, (tmpl, tinst)) =>
        if (newTemplate.structure.body == tmpl.structure.body) {
          val (blocker, cls) = encodeBlockers(Set(newTemplate.contents.pathVar._2, tmpl.contents.pathVar._2))
          val eqConds = (newTemplate.structure.locals zip tmpl.structure.locals)
            .filter(p => p._1 != p._2).map { case ((v, e1), (_, e2)) =>
              if (!unrollEquality(v.tpe)) mkEquals(e1, e2) else {
                registerEquality(blocker, v.tpe, e1, e2)
              }
            }
          val cond = mkAnd(blocker +: eqConds : _*)
          cls :+ mkImplies(cond, mkEquals(inst, tinst))
        } else {
          Seq.empty[Encoded]
        }
      }

      templates += newTemplate.structure -> ((newTemplate, inst))
      (mapping, clauses.toSeq)
    }
  }

  def promoteQuantifications: Unit = {
    val optGen = quantificationsManager.unrollGeneration
    if (optGen.isEmpty)
      throw FatalError("Attempting to promote inexistent quantifiers")

    val diff = (currentGeneration - optGen.get) max 0

    val currentGrounds = ignoredGrounds.toList
    ignoredGrounds.clear()
    for ((gen, qs) <- currentGrounds) {
      ignoredGrounds += (gen - diff) -> qs
    }

    val currentMatchers = ignoredMatchers.toList
    ignoredMatchers.clear()
    for ((gen, bs, m) <- currentMatchers) {
      ignoredMatchers += ((gen - diff, bs, m))
    }

    for (q <- quantifications if ignoredSubsts.isDefinedAt(q)) {
      ignoredSubsts += q -> ignoredSubsts(q).map { case (gen, bs, subst) => (gen - diff, bs, subst) }
    }
  }

  def requiresFiniteRangeCheck: Boolean =
    ignoredGrounds.nonEmpty || ignoredMatchers.nonEmpty || ignoredSubsts.exists(_._2.nonEmpty)

  def getFiniteRangeClauses: Clauses = {
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]
    val keyClause = MutableMap.empty[MatcherKey, (Clauses, Encoded)]

    val currentGrounds = ignoredGrounds.toList
    for ((gen, qs) <- currentGrounds if qs.exists(!_.hasAllGrounds)) {
      ignoredGrounds -= gen
      ignoredGrounds += currentGeneration -> qs
      clauses += falseT
    }

    for ((_, bs, m) <- ignoredMatchers.toList) {
      val key = matcherKey(m)
      val argTypes = key match {
        case tk: TypedKey =>
          val QuantificationTypeMatcher(argTypes, _) = tk.tpe
          argTypes
        case FunctionKey(tfd) =>
          tfd.params.map(_.getType) ++ (tfd.returnType match {
            case tpe @ QuantificationTypeMatcher(argTypes, _) if tpe.isInstanceOf[FunctionType] =>
              argTypes
            case _ => Seq.empty
          })
      }

      val (values, clause) = keyClause.getOrElse(key, {
        val insts = handledMatchers.toList.filter(hm => correspond(matcherKey(hm._2), key).isDefined)

        val guard = Variable.fresh("guard", BooleanType, true)
        val elems = argTypes.map(tpe => Variable.fresh("elem", tpe, true))
        val values = argTypes.map(tpe => Variable.fresh("value", tpe, true))
        val expr = andJoin(guard +: (elems zip values).map(p => Equals(p._1, p._2)))

        val guardP = guard -> encodeSymbol(guard)
        val elemsP = elems.map(e => e -> encodeSymbol(e))
        val valuesP = values.map(v => v -> encodeSymbol(v))
        val exprT = mkEncoder(elemsP.toMap ++ valuesP + guardP)(expr)

        val disjuncts = insts.map { case (bs, im) =>
          val cond = (m.key, im.key) match {
            case (Left((mcaller, _)), Left((imcaller, _))) if mcaller != imcaller =>
              Some(mkEquals(mcaller, imcaller))
            case _ => None
          }

          val bp = encodeEnablers(bs ++ cond)
          val subst = (elemsP.map(_._2) zip im.args.map(_.encoded)).toMap + (guardP._2 -> bp)
          mkSubstituter(subst)(exprT)
        }

        val res = (valuesP.map(_._2), if (disjuncts.isEmpty) falseT else mkOr(disjuncts : _*))
        keyClause += key -> res
        res
      })

      val b = encodeEnablers(bs)
      val substMap = (values zip m.args.map(_.encoded)).toMap
      clauses += mkSubstituter(substMap)(mkImplies(b, clause))
    }

    for (q <- quantifications if ignoredSubsts.isDefinedAt(q)) {
      val guard = Variable.fresh("guard", BooleanType, true)
      val elems = q.quantifiers.map(_._1)
      val values = elems.map(v => v.freshen)
      val expr = andJoin(guard +: (elems zip values).map(p => Equals(p._1, p._2)))

      val guardP = guard -> encodeSymbol(guard)
      val elemsP = elems.map(e => e -> encodeSymbol(e))
      val valuesP = values.map(v => v -> encodeSymbol(v))
      val exprT = mkEncoder(elemsP.toMap ++ valuesP + guardP)(expr)

      val disjunction = handledSubsts.getOrElse(q, Set.empty) match {
        case set if set.isEmpty => mkEncoder(Map.empty)(BooleanLiteral(false))
        case set => mkOr(set.toSeq.map { case (enablers, subst) =>
          val b = if (enablers.isEmpty) trueT else mkAnd(enablers.toSeq : _*)
          val substMap = (elemsP.map(_._2) zip q.quantifiers.map(p => subst(p._2).encoded)).toMap + (guardP._2 -> b)
          mkSubstituter(substMap)(exprT)
        } : _*)
      }

      for ((_, enablers, subst) <- ignoredSubsts(q)) {
        val b = if (enablers.isEmpty) trueT else mkAnd(enablers.toSeq : _*)
        val substMap = (valuesP.map(_._2) zip q.quantifiers.map(p => subst(p._2).encoded)).toMap
        clauses += mkSubstituter(substMap)(mkImplies(b, disjunction))
      }
    }

    clauses.toSeq
  }

  def getGroundInstantiations(e: Encoded, tpe: Type): Seq[(Encoded, Seq[Encoded])] = {
    val bestTpe = bestRealType(tpe)

    handledMatchers.toList.flatMap { case (bs, m) =>
      val enabler = encodeEnablers(bs)
      val optArgs = matcherKey(m) match {
        case tp: TypedKey if bestTpe == tp.tpe => Some(m.args.map(_.encoded))
        case _ => None
      }

      optArgs.map(args => enabler -> args)
    }
  }
}
