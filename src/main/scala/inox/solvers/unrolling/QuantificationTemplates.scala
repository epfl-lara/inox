/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._
import evaluators._

import scala.util.boundary
import scala.util.boundary._
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, Queue}

trait QuantificationTemplates { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import lambdasManager._
  import quantificationsManager._

  /* In this context, we know that all `Typing` instances correspond
   * to free constraint typings, so we are ensured that a result field
   * exists. The following helper extension enables simplified access to
   * that field.
   */
  extension (tp: Typing) {
    private def result: Encoded = {
      val Typing(_, _, Constraint(res, _, _)) = tp: @unchecked
      res
    }
  }

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
        body, stringRepr, isConcrete, isDeferred
      )

    def concretize: QuantificationTemplate = {
      assert(!isConcrete, "Can't concretize concrete quantification template")
      val substituter = mkSubstituter(structure.instantiationSubst)
      new QuantificationTemplate(polarity,
        contents.substitute(substituter, Map.empty),
        structure, body, stringRepr, true, isDeferred)
    }

    private lazy val str : String = stringRepr()
    override def toString : String = str
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
        mkExprStructure(pathVar._1, forall, substMap, onlySimple = !simpOpts.simplify): @unchecked

      val quantifiers = args.map(_.toVariable).toSet
      val idQuantifiers: Seq[Variable] = args.map(_.toVariable)
      val trQuantifiers: Seq[Encoded] = forall.params.map(v => encodeSymbol(v.toVariable))

      val clauseSubst: Map[Variable, Encoded] = depSubst ++ (idQuantifiers zip trQuantifiers)
      val (p, tmplClauses) = mkExprClauses(pathVar._1, body, clauseSubst)

      given TypingGenerator = if (pol) ContractGenerator else FreeGenerator
      val (tpeCond, tpeClauses) = idQuantifiers.foldLeft((BooleanLiteral(true): Expr, emptyClauses)) {
        case ((tpCond, tpClauses), v) =>
          val (p, clauses) = mkTypeClauses(pathVar._1, v.tpe, v, clauseSubst)
          (and(tpCond, p), tpClauses +++ clauses)
      }

      val clauses: TemplateClauses = tmplClauses +++ tpeClauses
      val (res, polarity, contents, str) = if (pol) {
        val subst = quantifiers.flatMap(v => typeOps.variablesOf(v.tpe)).map(v => v -> Left(clauseSubst(v))).toMap

        val (contents, str) = Template.contents(pathVar, idQuantifiers zip trQuantifiers,
          clauses + (pathVar._1 -> Implies(tpeCond, p)), depSubst)

        (BooleanLiteral(true), Positive(subst), contents, str)
      } else {
        val inst = Variable.fresh("inst", BooleanType(), true)
        val instT = encodeSymbol(inst)

        val (contents, str) = Template.contents(pathVar, idQuantifiers zip trQuantifiers,
          clauses + (pathVar._1 -> Equals(inst, Implies(tpeCond, p))), depSubst + (inst -> instT))

        (inst, Negative(inst -> instT), contents, str)
      }

      val template = new QuantificationTemplate(polarity, contents, structure, body,
        () => "Template for " + forall.asString + " is :\n" + str(), false, defer)

      (res, template)
    }
  }

  private[unrolling] object quantificationsManager extends Manager {
    private[QuantificationTemplates] val axioms = new IncrementalSeq[Axiom]

    private[QuantificationTemplates] val matcherBlockers = new IncrementalMap[Matcher, Encoded]
    private[QuantificationTemplates] val substBlockers   = new IncrementalMap[(Axiom, Map[Encoded, Arg]), Encoded]

    private[QuantificationTemplates] val ignoredMatchers = new IncrementalSeq[(Int, Set[Encoded], Matcher)]
    private[QuantificationTemplates] val ignoredSubsts   = new IncrementalMap[Axiom, Set[(Int, Set[Encoded], Map[Encoded,Arg])]]
    private[QuantificationTemplates] val ignoredGrounds  = new IncrementalMap[Int, Set[Axiom]]

    private[QuantificationTemplates] val lambdaAxioms    = new IncrementalSet[TemplateStructure]
    private[QuantificationTemplates] val templates       = new IncrementalMap[TemplateStructure, (QuantificationTemplate, Encoded)]

    val incrementals: Seq[IncrementalState] = Seq(axioms, lambdaAxioms, templates,
      matcherBlockers, substBlockers, ignoredMatchers, ignoredSubsts, ignoredGrounds)

    override def push(): Unit  = { super.push();  for (q <- axioms) q.push()  }
    override def pop(): Unit   = { super.pop();   for (q <- axioms) q.pop()   }
    override def clear(): Unit = { super.clear(); for (q <- axioms) q.clear() }
    override def reset(): Unit = { super.reset(); for (q <- axioms) q.reset() }

    override def satisfactionAssumptions = Seq()
    override def refutationAssumptions = Seq()

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
        clauses ++= instantiateMatcher0(bs, m, defer = true)
        ignoredMatchers -= e
      }

      reporter.debug("Unrolling ignored matchers (" + clauses.size + ")")
      for (cl <- clauses) {
        reporter.debug("  . " + cl)
      }

      if (abort || pause) return clauses.toSeq

      val suClauses = new scala.collection.mutable.ListBuffer[Encoded]
      for (q <- axioms.toSeq if ignoredSubsts.isDefinedAt(q) && !abort && !pause) {
        val (release, keep) = ignoredSubsts(q).partition(_._1 <= currentGeneration)
        ignoredSubsts += q -> keep

        for ((_, bs, subst) <- release) {
          suClauses ++= q.instantiateSubst(bs, subst, defer = true)
        }
      }

      reporter.debug("Unrolling ignored substitutions (" + suClauses.size + ")")
      for (cl <- suClauses) {
        reporter.debug("  . " + cl)
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

      reporter.debug("Unrolling ignored grounds (" + grClauses.size + ")")
      for (cl <- grClauses) {
        reporter.debug("  . " + cl)
      }

      clauses ++= grClauses

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
    if (abort || pause) {
      ignoredMatchers += ((currentGeneration, blockers, matcher))
      Seq.empty
    } else {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]

      val matcherBlocker = matcherBlockers.get(matcher) match {
        case Some(matcherBlocker) =>
          matcherBlocker

        case None =>
          val matcherBlocker = encodeSymbol(Variable.fresh("m", BooleanType(), true))
          matcherBlockers += matcher -> matcherBlocker

          reporter.debug(" -> instantiating matcher " + matcherBlocker + " ==> " + matcher)
          for (q <- axioms) clauses ++= q.instantiate(matcherBlocker, matcher, defer)
          matcherBlocker
      }

      if (blockers != Set(matcherBlocker)) {
        val (blocker, blockerClauses) = encodeBlockers(blockers)
        registerImplication(blocker, matcherBlocker)
        clauses ++= blockerClauses
        clauses += mkImplies(blocker, matcherBlocker)
      }

      clauses.toSeq
    }
  }

  def hasAxioms: Boolean = axioms.nonEmpty
  def getAxioms: Seq[Axiom] = axioms.toSeq

  def getInstantiationsWithBlockers = axioms.toSeq.flatMap(_.instantiations.toSeq)

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
  private class GroundSet extends Iterable[(Set[Encoded], Arg, Set[Int])] with IncrementalState {
    private val state = new IncrementalMap[Arg, (Set[Encoded], Set[Int])]

    def apply(bs: Set[Encoded], arg: Arg): Boolean = state.get(arg).exists(p => p._1 subsetOf bs)
    def +=(p: (Set[Encoded], Arg, Set[Int])): Unit = state.get(p._2) match {
      case Some((bs, gens)) =>
        val newBs: Set[Encoded] = bs ++ p._1
        val newGens: Set[Int] = if (gens.isEmpty || p._3.isEmpty) Set.empty else gens ++ p._3
        state += p._2 -> (newBs -> newGens)

      case None =>
        state += p._2 -> (p._1 -> p._3)
    }

    def iterator: Iterator[(Set[Encoded], Arg, Set[Int])] =
      state.iterator.map { case (arg, (bs, gens)) => (bs, arg, gens) }

    def push(): Unit = state.push()
    def pop(): Unit = state.pop()
    def clear(): Unit = state.clear()
    def reset(): Unit = state.reset()
  }

  private def totalDepth(m: Matcher): Int = 1 + m.args.map {
    case Right(ma) => totalDepth(ma)
    case _ => 0
  }.sum

  private def encodeEnablers(es: Set[Encoded]): Encoded =
    if (es.isEmpty) trueT else mkAnd(es.toSeq.sortBy(_.toString) : _*)

  private[solvers] class Axiom(
    contents: TemplateContents,
    subst: Map[Variable, Arg],
    val body: Expr,
    defer: Boolean) extends IncrementalState {

    private var _insts: Map[Encoded, Set[Encoded]] = Map.empty
    def instantiations = _insts

    private def registerBlockers(substituter: Encoded => Encoded): Unit = {
      val enabler = substituter(contents.pathVar._2)
      val bs = (contents.blockers.keys ++ contents.applications.keys).map(substituter).toSet
      _insts += enabler -> bs
    }

    lazy val quantifiers = contents.arguments
    lazy val quantified: Set[Encoded] = quantifiers.map(_._2).toSet
    lazy val pathBlockers = blockerPath(contents.pathVar._2)

    lazy val guard: Encoded = contents.pathVar._2

    private val keys: Seq[MatcherKey] = contents.matchers.flatMap(_._2.map(matcherKey)).toSeq
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
      val quantToGround: Map[Encoded, Set[(Set[Encoded], Arg, Set[Int])]] =
        for ((q, constraints) <- groupedConstraints) yield q -> {
          grounds(q).toSet ++ constraints.flatMap {
            case (key, i) => correspond(matcherKey(m), key).map {
              p => (Set(b), m.args(i), if (p) Set.empty[Int] else Set(gen))
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
        val newMappings = (quantified - q).foldLeft(Seq((Set(b), Map(q -> m.args(i)), initGens, 0))) {
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
            val substituter = mkSubstituter(map.view.mapValues(_.encoded).toMap)
            val msubst = map.collect { case (q, Right(m)) => q -> m }
            val opts = optimizationQuorums.flatMap { ms =>
              val sms = ms.map(_.substitute(substituter, msubst))
              if (sms.forall(sm => matcherBlockers contains sm)) sms.toList else Nil
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
        grounds(q) += ((Set(b), m.args(i), initGens))
      }

      instantiateSubsts(mappings)
    }

    def hasAllGrounds: Boolean = quantified.forall(q => grounds(q).nonEmpty)

    def ensureGrounds: Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]

      /* Build mappings from quantifiers to all potential ground values previously encountered
       * AND the constants we're introducing to make sure grounds are non-empty. */
      val quantToGround = (for ((v,q) <- quantifiers) yield {
        val groundsSet: Set[(Set[Encoded], Arg, Set[Int])] = grounds(q).toSet
        val newGrounds: Set[(Set[Encoded], Arg, Set[Int])] = {
          if (groundsSet.isEmpty) {
            Set((Set(), Left(q), Set()))
          } else {
            Set.empty
          }
        }

        q -> (groundsSet ++ newGrounds)
      }).toMap

      /* Generate the sequence of all relevant instantiation mappings */
      var mappings: Seq[(Set[Encoded], Map[Encoded, Arg], Int)] = Seq.empty
      for ((v,q) <- quantifiers if grounds(q).isEmpty) {
        val res: Set[Encoded] = if (FreeUnrolling unroll v.tpe) {
          val closures = typeOps.variablesOf(v.tpe).toSeq.sortBy(_.id).map(subst)
          val result = encodeSymbol(Variable.fresh("result", BooleanType(), true))
          clauses ++= instantiateType(contents.pathVar._2, Typing(v.tpe, q, Constraint(result, closures, true)))
          Set(result)
        } else {
          Set.empty
        }

        val init: Seq[(Set[Encoded], Map[Encoded, Arg], Set[Int], Int)] = Seq((res, Map(q -> Left(q)), Set(), 0))
        val newMappings = (quantified - q).foldLeft(init) { case (maps, oq) =>
          for ((bs, map, gens, c) <- maps; (ibs, inst, igens) <- quantToGround(oq)) yield {
            val delay = if (igens.isEmpty || (gens intersect igens).nonEmpty) 0 else 1
            (bs ++ ibs, map + (oq -> inst), gens ++ igens, c + delay)
          }
        }

        mappings ++= newMappings.map { case (bs, map, gens, c) =>
          (bs, map, c + (3 * map.values.collect { case Right(m) => totalDepth(m) }.sum))
        }

        grounds(q) += ((res, Left(q), Set.empty[Int]))
      }

      clauses ++= instantiateSubsts(mappings)
      clauses.toSeq
    }

    private def instantiateSubsts(substs: Seq[(Set[Encoded], Map[Encoded, Arg], Int)]): Clauses = {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]

      for (p @ (bs, subst, delay) <- substs if !substBlockers.get(this -> subst).exists(b => Set(b) == bs)) {
        if (abort || pause || delay > 0) {
          val gen = currentGeneration + delay + (if (defer) 2 else 0)
          ignoredSubsts += this -> (ignoredSubsts.getOrElse(this, Set.empty) + ((gen, bs, subst)))
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
          substBlockers += (this -> subst) -> substBlocker

          val (enabler, enablerClauses) = encodeBlockers(pathBlockers + substBlocker)
          clauses ++= enablerClauses

          val baseSubst = subst + (contents.pathVar._2 -> Left(enabler))
          val (substClauses, substMap) = contents.substitution(enabler, baseSubst)
          clauses ++= substClauses

          val msubst = substMap.collect { case (c, Right(m)) => c -> m }
          val substituter = mkSubstituter(substMap.view.mapValues(_.encoded).toMap)
          registerBlockers(substituter)

          // matcher instantiation must be manually controlled here to avoid never-ending loops
          clauses ++= Template.instantiate(
            contents.clauses, contents.blockers, contents.applications,
            Map.empty, contents.equalities, substMap)

          for ((b,ms) <- contents.matchers; m <- ms) {
            val sb = bs ++ (if (b == guard) Set.empty else Set(substituter(b)))
            val sm = m.substitute(substituter, msubst)

            if (abort || pause || b != guard) {
              val gen = currentGeneration + 1
              ignoredMatchers += ((gen, sb, sm))
            } else {
              clauses ++= instantiateMatcher0(sb, sm, defer = defer)
            }
          }

          substBlocker
      }

      if (bs != Set(substBlocker)) {
        val (blocker, blockerClauses) = encodeBlockers(bs)
        registerImplication(blocker, substBlocker)
        clauses ++= blockerClauses
        clauses += mkImplies(blocker, substBlocker)
      }

      clauses.toSeq
    }

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
      templates.collectFirst { case (s, t) if s subsumes template.structure => t }
    }.map { case (tmpl, inst) =>
      template.polarity match {
        case Positive(subst) =>
          (Map.empty[Encoded, Encoded], Seq(mkImplies(template.contents.pathVar._2, inst)))
        case Negative(insts) =>
          (Map(insts._2 -> inst), Seq.empty[Encoded])
      }
    }.getOrElse {
      reporter.debug("instantiating quantification " + template.body.asString)

      val newTemplate = template.concretize
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      clauses ++= newTemplate.structure.instantiation

      val (inst, mapping): (Encoded, Map[Encoded, Encoded]) = (newTemplate.polarity match {
        case Positive(subst) =>
          val axiom = new Axiom(newTemplate.contents, subst, newTemplate.body, newTemplate.isDeferred)
          axioms += axiom

          for ((m,b) <- matcherBlockers.toList) {
            clauses ++= axiom.instantiate(b, m)
          }

          val groundGen = currentGeneration + 3
          ignoredGrounds += groundGen -> (ignoredGrounds.getOrElse(groundGen, Set.empty) + axiom)
          (trueT, Map.empty)

        case Negative(insts) =>
          val instT = encodeSymbol(insts._1)
          val freshQuants = newTemplate.quantifiers.map(p => encodeSymbol(p._1))
          val substMap = ((newTemplate.quantifiers.map(_._2) :+ insts._2) zip (freshQuants :+ instT).map(Left(_))).toMap
          val (substClauses, fullSubst) = newTemplate.contents.substitution(newTemplate.contents.pathVar._2, substMap)
          clauses ++= substClauses

          // this will call `instantiateMatcher` on all matchers in `newTemplate.matchers`
          clauses ++= newTemplate.contents.instantiate(fullSubst)

          (instT, Map(insts._2 -> instT))
      }): @unchecked

      clauses ++= templates.flatMap { case (key, (tmpl, tinst)) =>
        if (typeOps.simplify(newTemplate.structure.body) == typeOps.simplify(tmpl.structure.body)) {
          val (blocker, cls) = encodeBlockers(Set(newTemplate.contents.pathVar._2, tmpl.contents.pathVar._2))
          val eqConds = (newTemplate.structure.locals zip tmpl.structure.locals)
            .filter(p => p._1 != p._2)
            .map { case ((v, e1), (_, e2)) =>
              val (equality, equalityClauses) = mkEqualities(blocker, v.getType, e1, e2, register = false)
              clauses ++= equalityClauses
              equality
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
      throw new InternalSolverError("Attempting to promote inexistent quantifiers")

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

    for (q <- axioms if ignoredSubsts.isDefinedAt(q)) {
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

        val res = (valuesP.map(_._2), if (disjuncts.isEmpty) falseT else mkOr(disjuncts : _*))
        keyClause += key -> res
        res
      })

      val b = encodeEnablers(bs)
      val substMap = (values zip m.args.map(_.encoded)).toMap
      clauses += mkSubstituter(substMap)(mkImplies(b, clause))
    }

    for (q <- axioms if ignoredSubsts.isDefinedAt(q)) {
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
    matcherBlockers.toList.flatMap { case (m, b) =>
      val optArgs = matcherKey(m) match {
        case tp: TypedKey if tpe == tp.tpe => Some(m.args.map(_.encoded))
        case _ => None
      }

      optArgs.map(args => b -> args)
    }
  }
}
