/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import ast.{Identifier, FreshIdentifier}
import utils._
import evaluators._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, Stack => MutableStack, Queue}

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
      case MultiplicityInBag(elem, bag) => Some(bag -> Seq(elem))
      case ElementOfSet(elem, set) => Some(set -> Seq(elem))
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
      case Positive(guardVar) => Positive(guardVar)
      case Negative(insts) => Negative(insts._1 -> substituter(insts._2))
      case Unknown(qs, q2s, insts, guardVar) => Unknown(qs._1 -> substituter(qs._2), q2s, insts, guardVar)
    }
  }

  case class Positive(guardVar: Encoded) extends Polarity
  case class Negative(insts: (Variable, Encoded)) extends Polarity
  case class Unknown(
    qs: (Variable, Encoded),
    q2s: (Variable, Encoded),
    insts: (Variable, Encoded),
    guardVar: Encoded) extends Polarity

  class QuantificationTemplate private[QuantificationTemplates] (
    val pathVar: (Variable, Encoded),
    val polarity: Polarity,
    val quantifiers: Seq[(Variable, Encoded)],
    val condVars: Map[Variable, Encoded],
    val exprVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: Calls,
    val applications: Apps,
    val matchers: Matchers,
    val lambdas: Seq[LambdaTemplate],
    val quantifications: Seq[QuantificationTemplate],
    val key: (Seq[ValDef], Expr, Seq[Encoded]),
    val body: Expr,
    stringRepr: () => String) {

    lazy val start = pathVar._2
    lazy val mapping: Map[Variable, Encoded] = polarity match {
      case Positive(_) => Map.empty
      case Negative(insts) => Map(insts)
      case Unknown(qs, _, _, _) => Map(qs)
    }

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]): QuantificationTemplate =
      new QuantificationTemplate(pathVar._1 -> substituter(start), polarity.substitute(substituter),
        quantifiers, condVars, exprVars, condTree, clauses.map(substituter),
        blockers.map { case (b, fis) => substituter(b) -> fis.map(_.substitute(substituter, msubst)) },
        applications.map { case (b, apps) => substituter(b) -> apps.map(_.substitute(substituter, msubst)) },
        matchers.map { case (b, ms) => substituter(b) -> ms.map(_.substitute(substituter, msubst)) },
        lambdas.map(_.substitute(substituter, msubst)),
        quantifications.map(_.substitute(substituter, msubst)),
        (key._1, key._2, key._3.map(substituter)),
        body, stringRepr)

    private lazy val str : String = stringRepr()
    override def toString : String = str
  }

  object QuantificationTemplate {
    def templateKey(quantifiers: Seq[ValDef], expr: Expr, substMap: Map[Variable, Encoded]): (Seq[ValDef], Expr, Seq[Encoded]) = {
      val (vals, struct, deps) = normalizeStructure(quantifiers, expr)
      val encoder = mkEncoder(substMap) _
      val depClosures = deps.toSeq.sortBy(_._1.id.uniqueName).map(p => encoder(p._2))
      (vals, struct, depClosures)
    }

    def apply(
      pathVar: (Variable, Encoded),
      optPol: Option[Boolean],
      p: Expr,
      quantifiers: Seq[(Variable, Encoded)],
      condVars: Map[Variable, Encoded],
      exprVars: Map[Variable, Encoded],
      condTree: Map[Variable, Set[Variable]],
      guardedExprs: Map[Variable, Seq[Expr]],
      lambdas: Seq[LambdaTemplate],
      quantifications: Seq[QuantificationTemplate],
      baseSubstMap: Map[Variable, Encoded],
      proposition: Forall
    ): (Option[Variable], QuantificationTemplate) = {

      val (optVar, polarity, extraGuarded, extraSubst) = optPol match {
        case Some(true) =>
          val guard: Variable = Variable(FreshIdentifier("guard", true), BooleanType)
          val guards = guard -> encodeSymbol(guard)
          (None, Positive(guards._2), Map(pathVar._1 -> Seq(Implies(guard, p))), Map(guards))

        case Some(false) =>
          val inst: Variable = Variable(FreshIdentifier("inst", true), BooleanType)
          val insts = inst -> encodeSymbol(inst)
          (Some(inst), Negative(insts), Map(pathVar._1 -> Seq(Equals(inst, p))), Map(insts))

        case None =>
          val q: Variable = Variable(FreshIdentifier("q", true), BooleanType)
          val q2: Variable = Variable(FreshIdentifier("qo", true), BooleanType)
          val inst: Variable = Variable(FreshIdentifier("inst", true), BooleanType)
          val guard: Variable = Variable(FreshIdentifier("guard", true), BooleanType)

          val qs = q -> encodeSymbol(q)
          val q2s = q2 -> encodeSymbol(q2)
          val insts = inst -> encodeSymbol(inst)
          val guards = guard -> encodeSymbol(guard)

          val polarity = Unknown(qs, q2s, insts, guards._2)
          val extraGuarded = Map(pathVar._1 -> Seq(Equals(inst, Implies(guard, p)), Equals(q, And(q2, inst))))
          val extraSubst = Map(qs, q2s, insts, guards)
          (Some(q), polarity, extraGuarded, extraSubst)
      }

      val substMap = baseSubstMap ++ extraSubst
      val allGuarded = guardedExprs merge extraGuarded

      val (clauses, blockers, applications, matchers, templateString) =
        Template.encode(pathVar, quantifiers, condVars, exprVars, allGuarded,
          lambdas, quantifications, substMap = substMap)

      val key = templateKey(proposition.args, proposition.body, substMap)

      (optVar, new QuantificationTemplate(
        pathVar, polarity, quantifiers, condVars, exprVars, condTree,
        clauses, blockers, applications, matchers, lambdas, quantifications, key,
        proposition.body, () => "Template for " + proposition + " is :\n" + templateString()))
    }
  }

  private[unrolling] object quantificationsManager extends Manager {
    val quantifications = new IncrementalSeq[Quantification]

    val ignoredMatchers = new IncrementalSeq[(Int, Set[Encoded], Matcher)]

    // to avoid [[MatcherSet]] escaping defining context, we must keep this ~private
    private[QuantificationTemplates] val handledMatchers = new MatcherSet

    val ignoredSubsts   = new IncrementalMap[Quantification, Set[(Int, Set[Encoded], Map[Encoded,Arg])]]
    val handledSubsts   = new IncrementalMap[Quantification, Set[(Set[Encoded], Map[Encoded,Arg])]]
    val ignoredGrounds  = new IncrementalMap[Int, Set[Quantification]]

    val lambdaAxioms    = new IncrementalSet[(LambdaStructure, Seq[(Variable, Encoded)])]
    val templates       = new IncrementalMap[(Seq[ValDef], Expr, Seq[Encoded]), Map[Encoded, Encoded]]

    val incrementals: Seq[IncrementalState] = Seq(
      quantifications, ignoredMatchers, handledMatchers, ignoredSubsts, handledSubsts, lambdaAxioms, templates)

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

      for (e @ (gen, bs, m) <- ignoredMatchers.toSeq if gen <= currentGeneration) {
        clauses ++= instantiateMatcher(bs, m)
        ignoredMatchers -= e
      }

      for (q <- quantifications.toSeq if ignoredSubsts.isDefinedAt(q)) {
        val (release, keep) = ignoredSubsts(q).partition(_._1 <= currentGeneration)
        ignoredSubsts += q -> keep

        for ((_, bs, subst) <- release) {
          clauses ++= q.instantiateSubst(bs, subst)
        }
      }

      for ((gen, qs) <- ignoredGrounds.toSeq if gen <= currentGeneration; q <- qs) {
        clauses ++= q.ensureGrounds
        ignoredGrounds += gen -> (ignoredGrounds.getOrElse(gen, Set.empty) - q)
      }

      clauses.toSeq
    }
  }

  def instantiateMatcher(blocker: Encoded, matcher: Matcher): Clauses =
    instantiateMatcher(Set(blocker), matcher)

  @inline
  private def instantiateMatcher(blockers: Set[Encoded], matcher: Matcher): Clauses = {
    if (handledMatchers(blockers -> matcher)) {
      Seq.empty
    } else {
      handledMatchers += blockers -> matcher
      quantifications.flatMap(_.instantiate(blockers, matcher))
    }
  }

  def hasQuantifiers: Boolean = quantifications.nonEmpty

  def getInstantiationsWithBlockers = quantifications.toSeq.flatMap {
    case q: GeneralQuantification => q.instantiations.toSeq
    case _ => Seq.empty
  }

  private sealed trait MatcherKey
  private case class FunctionKey(tfd: TypedFunDef) extends MatcherKey
  private sealed abstract class TypedKey(val tpe: Type) extends MatcherKey
  private case class LambdaKey(lambda: Lambda, tt: Type) extends TypedKey(tt)
  private case class CallerKey(caller: Encoded, tt: Type) extends TypedKey(tt)
  private case class TypeKey(tt: Type) extends TypedKey(tt)

  private def matcherKey(key: Either[(Encoded, Type), TypedFunDef]): MatcherKey = key match {
    case Right(tfd) => FunctionKey(tfd)
    case Left((caller, ft: FunctionType)) if byID.isDefinedAt(caller) => LambdaKey(byID(caller).structure.lambda, ft)
    case Left((caller, ft: FunctionType)) => CallerKey(caller, ft)
    case Left((_, tpe)) => TypeKey(tpe)
  }

  @inline
  private def matcherKey(m: Matcher): MatcherKey = matcherKey(m.key)

  private def correspond(k1: MatcherKey, k2: MatcherKey): Option[Boolean] = (k1, k2) match {
    case (`k2`, _) => Some(true)
    case (tp1: TypedKey, tp2: TypedKey) if tp1.tpe == tp2.tpe => Some(false)
    case _ => None
  }

  @inline
  private def correspond(m1: Matcher, m2: Matcher): Option[Boolean] =
    correspond(matcherKey(m1), matcherKey(m2))

  private trait BlockedSet[Element] extends Iterable[(Set[Encoded], Element)] with IncrementalState {
    private var map: MutableMap[Any, (Element, MutableSet[Set[Encoded]])] = MutableMap.empty
    private val stack = new MutableStack[MutableMap[Any, (Element, MutableSet[Set[Encoded]])]]

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
      stack.push(map)
      map = newMap
    }

    def pop(): Unit = {
      map = stack.pop()
    }

    def clear(): Unit = {
      stack.clear()
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

  private class MatcherSet extends BlockedSet[Matcher]

  private def totalDepth(m: Matcher): Int = 1 + m.args.map {
    case Right(ma) => totalDepth(ma)
    case _ => 0
  }.sum

  private def encodeEnablers(es: Set[Encoded]): Encoded =
    if (es.isEmpty) trueT else mkAnd(es.toSeq.sortBy(_.toString) : _*)

  private[solvers] trait Quantification extends IncrementalState {
    val pathVar: (Variable, Encoded)
    val quantifiers: Seq[(Variable, Encoded)]
    val condVars: Map[Variable, Encoded]
    val exprVars: Map[Variable, Encoded]
    val condTree: Map[Variable, Set[Variable]]
    val clauses: Clauses
    val blockers: Calls
    val applications: Apps
    val matchers: Matchers
    val lambdas: Seq[LambdaTemplate]
    val quantifications: Seq[QuantificationTemplate]

    val holds: Encoded
    val body: Expr

    lazy val quantified: Set[Encoded] = quantifiers.map(_._2).toSet
    lazy val start = pathVar._2

    private val constraints: Seq[(Encoded, MatcherKey, Int)] = (for {
      (_, ms) <- matchers
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

    def instantiate(bs: Set[Encoded], m: Matcher): Clauses = {

      generationCounter += 1
      val gen = generationCounter

      /* Build mappings from quantifiers to all potential ground values previously encountered. */
      val quantToGround: Map[Encoded, Set[(Set[Encoded], Arg, Set[Int])]] =
        for ((q, constraints) <- groupedConstraints) yield q -> {
          grounds(q).unzipSet ++
          constraints.flatMap { case (key, i) =>
            correspond(matcherKey(m), key).map(p => (bs, m.args(i), if (p) Set.empty[Int] else Set(gen)))
          }
        }

      /* Transform the map to sets into a sequence of maps making sure that the current
       * matcher is part of the mapping (otherwise, instantiation has already taken place). */
      var mappings: Seq[(Set[Encoded], Map[Encoded, Arg], Int)] = Seq.empty
      for ((q, constraints) <- groupedConstraints;
           (key, i) <- constraints;
           perfect <- correspond(matcherKey(m), key)
           if !grounds(q)(bs, m.args(i))) {
        val initGens: Set[Int] = if (perfect) Set.empty else Set(gen)
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

        mappings ++= newMappings.map { case (bs, map, gens, c) => (bs, map, c) }

        // register ground instantiation for future instantiations
        grounds(q) += ((bs, m.args(i), initGens))
      }

      instantiateSubsts(mappings)
    }

    def ensureGrounds: Clauses = {
      /* Build mappings from quantifiers to all potential ground values previously encountered
       * AND the constants we're introducing to make sure grounds are non-empty. */
      val quantToGround = (for (q <- quantified) yield {
        val groundsSet: Set[(Set[Encoded], Arg, Set[Int])] = grounds(q).unzipSet
        val newGrounds: Set[(Set[Encoded], Arg, Set[Int])] = {
          if (groundsSet.isEmpty) Set((Set(), Left(q), Set()))
          else Set.empty
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

        mappings ++= newMappings.map { case (bs, map, gens, c) => (bs, map, c) }

        grounds(q) += ((Set.empty[Encoded], Left(q), Set.empty[Int]))
      }

      instantiateSubsts(mappings)
    }

    private def instantiateSubsts(substs: Seq[(Set[Encoded], Map[Encoded, Arg], Int)]): Clauses = {
      val instantiation = new scala.collection.mutable.ListBuffer[Encoded]

      for (p @ (bs, subst, delay) <- substs if !handledSubsts.get(this).exists(_ contains (bs -> subst))) {
        val totalDelay = delay + (3 * subst.values.collect { case Right(m) => totalDepth(m) }.sum)
        if (totalDelay > 0) {
          val gen = currentGeneration + totalDelay
          ignoredSubsts += this -> (ignoredSubsts.getOrElse(this, Set.empty) + ((gen, bs, subst)))
        } else {
          instantiation ++= instantiateSubst(bs, subst)
        }
      }

      instantiation.toSeq
    }

    def instantiateSubst(bs: Set[Encoded], subst: Map[Encoded, Arg]): Clauses = {
      handledSubsts += this -> (handledSubsts.getOrElse(this, Set.empty) + (bs -> subst))
      val instantiation = new scala.collection.mutable.ListBuffer[Encoded]

      val (enabler, enablerClauses) = encodeBlockers(bs)
      instantiation ++= enablerClauses

      val baseSubst = subst ++ instanceSubst(enabler).mapValues(Left(_))
      val (substMap, substClauses) = Template.substitution(
        condVars, exprVars, condTree, lambdas, quantifications, baseSubst, pathVar._1, enabler)
      instantiation ++= substClauses

      val msubst = substMap.collect { case (c, Right(m)) => c -> m }
      val substituter = mkSubstituter(substMap.mapValues(_.encoded))
      registerBlockers(substituter)

      // matcher instantiation must be manually controlled here to avoid never-ending loops
      instantiation ++= Template.instantiate(clauses, blockers, applications, Map.empty, substMap)

      for ((b,ms) <- matchers; m <- ms) {
        val sb = bs ++ (if (b == start) Set.empty else Set(substituter(b)))
        val sm = m.substitute(substituter, msubst)

        def abs(i: Int): Int = if (i < 0) -i else i
        val nextGeneration: Int = currentGeneration +
          2 * (abs(totalDepth(sm) - totalDepth(m)) + (if (b == start) 0 else 1))

        if (nextGeneration == currentGeneration) {
          instantiation ++= instantiateMatcher(sb, sm)
        } else {
          ignoredMatchers += ((nextGeneration, sb, sm))
        }
      }

      instantiation.toSeq
    }

    protected def instanceSubst(enabler: Encoded): Map[Encoded, Encoded]

    protected def registerBlockers(substituter: Encoded => Encoded): Unit = ()

    def checkForall: Option[String] = {
      val quantified = quantifiers.map(_._1).toSet

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

      val bijectiveMappings = matcherToQuants.filter(_._2.nonEmpty).groupBy(_._2)
      if (bijectiveMappings.size > 1)
        return Some("Non-bijective mapping for symbol " + bijectiveMappings.head._2.head._1.asString)

      def quantifiedArg(e: Expr): Boolean = e match {
        case v: Variable => quantified(v)
        case QuantificationMatcher(_, args) => args.forall(quantifiedArg)
        case _ => false
      }

      exprOps.postTraversal(m => m match {
        case QuantificationMatcher(_, args) =>
          val qArgs = args.filter(quantifiedArg)

          if (qArgs.nonEmpty && qArgs.size < args.size)
            return Some("Mixed ground and quantified arguments in " + m.asString)

        case Operator(es, _) if es.collect { case v: Variable if quantified(v) => v }.nonEmpty =>
          return Some("Invalid operation on quantifiers " + m.asString)

        case (_: Equals) | (_: And) | (_: Or) | (_: Implies) | (_: Not) => // OK

        case Operator(es, _) if (es.flatMap(exprOps.variablesOf).toSet & quantified).nonEmpty =>
          return Some("Unandled implications from operation " + m.asString)

        case _ =>
      }) (body)

      body match {
        case v: Variable if quantified(v) =>
          Some("Unexpected free quantifier " + v.asString)
        case _ => None
      }
    }
  }

  private class GeneralQuantification (
    val pathVar: (Variable, Encoded),
    val qs: (Variable, Encoded),
    val q2s: (Variable, Encoded),
    val insts: (Variable, Encoded),
    val guardVar: Encoded,
    val quantifiers: Seq[(Variable, Encoded)],
    val condVars: Map[Variable, Encoded],
    val exprVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: Calls,
    val applications: Apps,
    val matchers: Matchers,
    val lambdas: Seq[LambdaTemplate],
    val quantifications: Seq[QuantificationTemplate],
    val body: Expr) extends Quantification {

    private var _currentQ2Var: Encoded = qs._2
    def currentQ2Var = _currentQ2Var
    val holds = qs._2

    private var _insts: Map[Encoded, Set[Encoded]] = Map.empty
    def instantiations = _insts

    private val blocker = Variable(FreshIdentifier("b_fresh", true), BooleanType)
    protected def instanceSubst(enabler: Encoded): Map[Encoded, Encoded] = {
      val nextQ2Var = encodeSymbol(q2s._1)

      val subst = Map(qs._2 -> currentQ2Var, guardVar -> enabler,
        q2s._2 -> nextQ2Var, insts._2 -> encodeSymbol(insts._1))

      _currentQ2Var = nextQ2Var
      subst
    }

    override def registerBlockers(substituter: Encoded => Encoded): Unit = {
      val freshInst = substituter(insts._2)
      val bs = (blockers.keys ++ applications.keys).map(substituter).toSet
      _insts += freshInst -> bs
    }
  }

  private class Axiom (
    val pathVar: (Variable, Encoded),
    val guardVar: Encoded,
    val quantifiers: Seq[(Variable, Encoded)],
    val condVars: Map[Variable, Encoded],
    val exprVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: Calls,
    val applications: Apps,
    val matchers: Matchers,
    val lambdas: Seq[LambdaTemplate],
    val quantifications: Seq[QuantificationTemplate],
    val body: Expr) extends Quantification {

    val holds = trueT

    protected def instanceSubst(enabler: Encoded): Map[Encoded, Encoded] = {
      Map(guardVar -> enabler)
    }
  }

  def instantiateAxiom(template: LambdaTemplate): Clauses = {
    val quantifiers = template.arguments.map { p => p._1.freshen -> encodeSymbol(p._1) }

    val app = mkApplication(template.ids._1, quantifiers.map(_._1))
    val appT = mkEncoder(quantifiers.toMap + template.ids)(app)
    val selfMatcher = Matcher(Left(template.ids._2 -> template.tpe), quantifiers.map(p => Left(p._2)), appT)

    val blocker = Variable(FreshIdentifier("blocker", true), BooleanType)
    val blockerT = encodeSymbol(blocker)

    val guard = Variable(FreshIdentifier("guard", true), BooleanType)
    val guardT = encodeSymbol(guard)

    val enablingClause = mkEquals(mkAnd(guardT, template.start), blockerT)

    /* Compute Axiom's unique key to avoid redudant instantiations */

    def flattenLambda(e: Expr): (Seq[ValDef], Expr) = e match {
      case Lambda(args, body) =>
        val (recArgs, recBody) = flattenLambda(body)
        (args ++ recArgs, recBody)
      case _ => (Seq.empty, e)
    }

    val (structArgs, structBody) = flattenLambda(template.structure.lambda)
    assert(quantifiers.size == structArgs.size, "Expecting lambda templates to contain flattened lamdbas")

    val lambdaBody = exprOps.replaceFromSymbols((structArgs zip quantifiers.map(_._1)).toMap, structBody)
    val quantBody = Equals(app, lambdaBody)

    val substMap = template.structure.locals.toMap + template.ids

    val key = QuantificationTemplate.templateKey(quantifiers.map(_._1.toVal), quantBody, substMap)

    val substituter = mkSubstituter((template.args zip quantifiers.map(_._2)).toMap + (template.start -> blockerT))
    val msubst = Map.empty[Encoded, Matcher]

    instantiateQuantification(new QuantificationTemplate(
      template.pathVar,
      Positive(guardT),
      quantifiers,
      template.condVars + (blocker -> blockerT),
      template.exprVars,
      template.condTree,
      (template.clauses map substituter) :+ enablingClause,
      template.blockers.map { case (b, fis) => substituter(b) -> fis.map(_.substitute(substituter, msubst)) },
      template.applications.map { case (b, fas) => substituter(b) -> fas.map(_.substitute(substituter, msubst)) },
      template.matchers.map { case (b, ms) =>
        substituter(b) -> ms.map(_.substitute(substituter, msubst))
      } merge Map(blockerT -> Set(selfMatcher)),
      template.lambdas.map(_.substitute(substituter, msubst)),
      template.quantifications.map(_.substitute(substituter, msubst)),
      key, quantBody, template.stringRepr))._2 // mapping is guaranteed empty!!
  }

  def instantiateQuantification(template: QuantificationTemplate): (Map[Encoded, Encoded], Clauses) = {
    templates.get(template.key) match {
      case Some(map) =>
        (map, Seq.empty)

      case None =>
        val clauses = new scala.collection.mutable.ListBuffer[Encoded]
        val mapping: Map[Encoded, Encoded] = template.polarity match {
          case Positive(guardVar) =>
            val axiom = new Axiom(template.pathVar, guardVar,
              template.quantifiers, template.condVars, template.exprVars, template.condTree,
              template.clauses, template.blockers, template.applications, template.matchers,
              template.lambdas, template.quantifications, template.body)

            quantifications += axiom

            for ((bs,m) <- handledMatchers) {
              clauses ++= axiom.instantiate(bs, m)
            }

            val groundGen = currentGeneration + 3
            ignoredGrounds += groundGen -> (ignoredGrounds.getOrElse(groundGen, Set.empty) + axiom)
            Map.empty

          case Negative(insts) =>
            val instT = encodeSymbol(insts._1)
            val (substMap, substClauses) = Template.substitution(
              template.condVars, template.exprVars, template.condTree,
              template.lambdas, template.quantifications,
              Map(insts._2 -> Left(instT)), template.pathVar._1, template.pathVar._2)
            clauses ++= substClauses

            // this will call `instantiateMatcher` on all matchers in `template.matchers`
            val instClauses = Template.instantiate(template.clauses,
              template.blockers, template.applications, template.matchers, substMap)
            clauses ++= instClauses

            Map(insts._2 -> instT)

          case Unknown(qs, q2s, insts, guardVar) =>
            val qT = encodeSymbol(qs._1)
            val substituter = mkSubstituter(Map(qs._2 -> qT))

            val quantification = new GeneralQuantification(template.pathVar,
              qs._1 -> qT, q2s, insts, guardVar,
              template.quantifiers, template.condVars, template.exprVars, template.condTree,
              template.clauses map substituter, // one clause depends on 'qs._2' (and therefore 'qT')
              template.blockers, template.applications, template.matchers,
              template.lambdas, template.quantifications, template.body)

            quantifications += quantification

            for ((bs,m) <- handledMatchers) {
              clauses ++= quantification.instantiate(bs, m)
            }

            for ((b,ms) <- template.matchers; m <- ms) {
              clauses ++= instantiateMatcher(b, m)
            }

            clauses ++= quantification.ensureGrounds
            Map(qs._2 -> qT)
        }

        templates += template.key -> mapping
        (mapping, clauses.toSeq)
    }
  }

  def promoteQuantifications: Unit = {
    val optGen = quantificationsManager.unrollGeneration
    if (optGen.isEmpty)
      throw FatalError("Attempting to promote inexistent quantifiers")

    val diff = (currentGeneration - optGen.get) max 0
    val currentMatchers = ignoredMatchers.toSeq
    ignoredMatchers.clear()
    for ((gen, bs, m) <- currentMatchers) {
      ignoredMatchers += ((gen - diff, bs, m))
    }

    for (q <- quantifications) {
      ignoredSubsts += q -> ignoredSubsts(q).map { case (gen, bs, subst) => (gen - diff, bs, subst) }
    }
  }

  def requiresFiniteRangeCheck: Boolean =
    ignoredMatchers.nonEmpty || ignoredSubsts.exists(_._2.nonEmpty)

  def getFiniteRangeClauses: Clauses = {
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]
    val keyClause = MutableMap.empty[MatcherKey, (Clauses, Encoded)]

    for ((_, bs, m) <- ignoredMatchers) {
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
        val insts = handledMatchers.filter(hm => correspond(matcherKey(hm._2), key).isDefined)

        val guard = Variable(FreshIdentifier("guard", true), BooleanType)
        val elems = argTypes.map(tpe => Variable(FreshIdentifier("elem", true), tpe))
        val values = argTypes.map(tpe => Variable(FreshIdentifier("value", true), tpe))
        val expr = andJoin(guard +: (elems zip values).map(p => Equals(p._1, p._2)))

        val guardP = guard -> encodeSymbol(guard)
        val elemsP = elems.map(e => e -> encodeSymbol(e))
        val valuesP = values.map(v => v -> encodeSymbol(v))
        val exprT = mkEncoder(elemsP.toMap ++ valuesP + guardP)(expr)

        val disjuncts = insts.toSeq.map { case (bs, im) =>
          val cond = (m.key, im.key) match {
            case (Left((mcaller, _)), Left((imcaller, _))) if mcaller != imcaller =>
              Some(mkEquals(mcaller, imcaller))
            case _ => None
          }

          val bp = encodeEnablers(bs ++ cond)
          val subst = (elemsP.map(_._2) zip im.args.map(_.encoded)).toMap + (guardP._2 -> bp)
          mkSubstituter(subst)(exprT)
        }

        val res = (valuesP.map(_._2), mkOr(disjuncts : _*))
        keyClause += key -> res
        res
      })

      val b = encodeEnablers(bs)
      val substMap = (values zip m.args.map(_.encoded)).toMap
      clauses += mkSubstituter(substMap)(mkImplies(b, clause))
    }

    for (q <- quantifications) {
      val guard = Variable(FreshIdentifier("guard", true), BooleanType)
      val elems = q.quantifiers.map(_._1)
      val values = elems.map(v => v.freshen)
      val expr = andJoin(guard +: (elems zip values).map(p => Equals(p._1, p._2)))

      val guardP = guard -> encodeSymbol(guard)
      val elemsP = elems.map(e => e -> encodeSymbol(e))
      val valuesP = values.map(v => v -> encodeSymbol(v))
      val exprT = mkEncoder(elemsP.toMap ++ valuesP + guardP)(expr)

      val disjunction = handledSubsts(q) match {
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
    handledMatchers.toSeq.flatMap { case (bs, m) =>
      val enabler = encodeEnablers(bs)
      val optArgs = matcherKey(m) match {
        case tp: TypedKey if bestTpe == tp.tpe => Some(m.args.map(_.encoded))
        case _ => None
      }

      optArgs.map(args => enabler -> args)
    }
  }
}
