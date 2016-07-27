/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, Stack => MutableStack, Queue}

trait QuantificationTemplates { self: Templates =>
  import program._
  import program.trees._
  import program.symbols._

  import lambdasManager._
  import quantificationsManager._

  def hasQuantifiers = quantifications.nonEmpty

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

  class QuantificationTemplate(
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
    val structure: Forall,
    val dependencies: Map[Variable, Encoded],
    val forall: Forall,
    stringRepr: () => String) {

    lazy val start = pathVar._2
    lazy val key: (Forall, Seq[Encoded]) = (structure, {
      var cls: Seq[Encoded] = Seq.empty
      exprOps.preTraversal {
        case v: Variable => cls ++= dependencies.get(v)
        case _ =>
      } (structure)
      cls
    })

    def substitute(substituter: Encoded => Encoded, msubst: Map[Encoded, Matcher]) = new QuantificationTemplate(
      pathVar._1 -> substituter(start),
      qs, q2s, insts, guardVar, quantifiers, condVars, exprVars, condTree,
      clauses.map(substituter),
      blockers.map { case (b, fis) => substituter(b) -> fis.map(_.substitute(substituter, msubst)) },
      applications.map { case (b, apps) => substituter(b) -> apps.map(_.substitute(substituter, msubst)) },
      matchers.map { case (b, ms) => substituter(b) -> ms.map(_.substitute(substituter, msubst)) },
      lambdas.map(_.substitute(substituter, msubst)),
      structure, dependencies.map { case (id, value) => id -> substituter(value) },
      forall, stringRepr)

    private lazy val str : String = stringRepr()
    override def toString : String = str
  }

  object QuantificationTemplate {
    def apply(
      pathVar: (Variable, Encoded),
      qs: (Variable, Encoded),
      q2: Variable,
      inst: Variable,
      guard: Variable,
      quantifiers: Seq[(Variable, Encoded)],
      condVars: Map[Variable, Encoded],
      exprVars: Map[Variable, Encoded],
      condTree: Map[Variable, Set[Variable]],
      guardedExprs: Map[Variable, Seq[Expr]],
      lambdas: Seq[LambdaTemplate],
      baseSubstMap: Map[Variable, Encoded],
      dependencies: Map[Variable, Encoded],
      proposition: Forall
    ): QuantificationTemplate = {

      val q2s: (Variable, Encoded) = q2 -> encodeSymbol(q2)
      val insts: (Variable, Encoded) = inst -> encodeSymbol(inst)
      val guards: (Variable, Encoded) = guard -> encodeSymbol(guard)

      val (clauses, blockers, applications, matchers, templateString) =
        Template.encode(pathVar, quantifiers, condVars, exprVars, guardedExprs, lambdas, Seq.empty,
          substMap = baseSubstMap + q2s + insts + guards + qs)

      val (structuralQuant, deps) = normalizeStructure(proposition)
      val keyDeps = deps.map { case (id, dep) => id -> encodeExpr(dependencies)(dep) }

      new QuantificationTemplate(
        pathVar, qs, q2s, insts, guards._2, quantifiers, condVars, exprVars, condTree,
        clauses, blockers, applications, matchers, lambdas, structuralQuant, keyDeps, proposition,
        () => "Template for " + proposition + " is :\n" + templateString())
    }
  }

  private[unrolling] object quantificationsManager extends Manager {
    val quantifications = new IncrementalSeq[MatcherQuantification]

    private[QuantificationTemplates] val instCtx = new InstantiationContext

    val ignoredMatchers = new IncrementalSeq[(Int, Set[Encoded], Matcher)]
    val ignoredSubsts   = new IncrementalMap[MatcherQuantification, MutableSet[(Int, Set[Encoded], Map[Encoded,Arg])]]
    val handledSubsts   = new IncrementalMap[MatcherQuantification, MutableSet[(Set[Encoded], Map[Encoded,Arg])]]

    val lambdaAxioms    = new IncrementalSet[(LambdaStructure, Seq[(Variable, Encoded)])]
    val templates       = new IncrementalMap[(Expr, Seq[Encoded]), Encoded]

    val incrementals: Seq[IncrementalState] = Seq(
      quantifications, instCtx, ignoredMatchers, ignoredSubsts,
      handledSubsts, lambdaAxioms, templates)

    private def assumptions: Seq[Encoded] =
      quantifications.collect { case q: Quantification => q.currentQ2Var }.toSeq
    def satisfactionAssumptions = assumptions
    def refutationAssumptions = assumptions
  }

  private var currentGen = 0

  private sealed abstract class MatcherKey(val tpe: Type)
  private case class CallerKey(caller: Encoded, tt: Type) extends MatcherKey(tt)
  private case class LambdaKey(lambda: Lambda, tt: Type) extends MatcherKey(tt)
  private case class TypeKey(tt: Type) extends MatcherKey(tt)

  private def matcherKey(caller: Encoded, tpe: Type): MatcherKey = tpe match {
    case ft: FunctionType if knownFree(ft)(caller) => CallerKey(caller, tpe)
    case _: FunctionType if byID.isDefinedAt(caller) => LambdaKey(byID(caller).structure.lambda, tpe)
    case _ => TypeKey(tpe)
  }

  @inline
  private def correspond(qm: Matcher, m: Matcher): Boolean =
    correspond(qm, m.caller, m.tpe)

  private def correspond(qm: Matcher, caller: Encoded, tpe: Type): Boolean = {
    val qkey = matcherKey(qm.caller, qm.tpe)
    val key = matcherKey(caller, tpe)
    qkey == key || (qkey.tpe == key.tpe && (qkey.isInstanceOf[TypeKey] || key.isInstanceOf[TypeKey]))
  }

  class VariableNormalizer {
    private val varMap: MutableMap[Type, Seq[Encoded]] = MutableMap.empty
    private val varSet: MutableSet[Encoded]            = MutableSet.empty

    def normalize(ids: Seq[Variable]): Seq[Encoded] = {
      val mapping = ids.groupBy(id => bestRealType(id.getType)).flatMap { case (tpe, idst) =>
        val prev = varMap.get(tpe) match {
          case Some(seq) => seq
          case None => Seq.empty
        }

        if (prev.size >= idst.size) {
          idst zip prev.take(idst.size)
        } else {
          val (handled, newIds) = idst.splitAt(prev.size)
          val uIds = newIds.map(id => id -> encodeSymbol(id))

          varMap(tpe) = prev ++ uIds.map(_._2)
          varSet ++= uIds.map(_._2)

          (handled zip prev) ++ uIds
        }
      }.toMap

      ids.map(mapping)
    }

    def normalSubst(qs: Seq[(Variable, Encoded)]): Map[Encoded, Encoded] = {
      (qs.map(_._2) zip normalize(qs.map(_._1))).toMap
    }

    def contains(idT: Encoded): Boolean = varSet(idT)
    def get(tpe: Type): Option[Seq[Encoded]] = varMap.get(tpe)
  }

  private val abstractNormalizer = new VariableNormalizer
  private val concreteNormalizer = new VariableNormalizer

  def isQuantifier(idT: Encoded): Boolean = abstractNormalizer.contains(idT)

  def typeInstantiations: Map[Type, MatcherSet] = instCtx.map.instantiations.collect {
    case (TypeKey(tpe), matchers) => tpe -> matchers
  }

  def lambdaInstantiations: Map[Lambda, MatcherSet] = instCtx.map.instantiations.collect {
    case (LambdaKey(lambda, tpe), matchers) => lambda -> (matchers ++ instCtx.map.get(TypeKey(tpe)).toMatchers)
  }

  def partialInstantiations: Map[Encoded, MatcherSet] = instCtx.map.instantiations.collect {
    case (CallerKey(caller, tpe), matchers) => caller -> (matchers ++ instCtx.map.get(TypeKey(tpe)).toMatchers)
  }

  private def maxDepth(m: Matcher): Int = 1 + (0 +: m.args.map {
    case Right(ma) => maxDepth(ma)
    case _ => 0
  }).max

  private def totalDepth(m: Matcher): Int = 1 + m.args.map {
    case Right(ma) => totalDepth(ma)
    case _ => 0
  }.sum

  private def encodeEnablers(es: Set[Encoded]): Encoded =
    if (es.isEmpty) trueT else mkAnd(es.toSeq.sortBy(_.toString) : _*)

  private type MatcherSet = Set[(Encoded, Matcher)]

  private class Context private(ctx: Map[Matcher, Set[Set[Encoded]]]) extends Iterable[(Set[Encoded], Matcher)] {
    def this() = this(Map.empty)

    def apply(p: (Set[Encoded], Matcher)): Boolean = ctx.get(p._2) match {
      case None => false
      case Some(blockerSets) => blockerSets(p._1) || blockerSets.exists(set => set.subsetOf(p._1))
    }

    def +(p: (Set[Encoded], Matcher)): Context = if (apply(p)) this else {
      val prev = ctx.getOrElse(p._2, Set.empty)
      val newSet = prev.filterNot(set => p._1.subsetOf(set)).toSet + p._1
      new Context(ctx + (p._2 -> newSet))
    }

    def ++(that: Context): Context = that.foldLeft(this)((ctx, p) => ctx + p)

    def iterator = ctx.toSeq.flatMap { case (m, bss) => bss.map(bs => bs -> m) }.iterator
    def toMatchers: MatcherSet = this.map(p => encodeEnablers(p._1) -> p._2).toSet
  }

  private class ContextMap(
    private var tpeMap: MutableMap[Type, Context]   = MutableMap.empty,
    private var funMap: MutableMap[MatcherKey, Context] = MutableMap.empty
  ) extends IncrementalState {
    private val stack = new MutableStack[(MutableMap[Type, Context], MutableMap[MatcherKey, Context])]

    def clear(): Unit = {
      stack.clear()
      tpeMap.clear()
      funMap.clear()
    }

    def reset(): Unit = clear()

    def push(): Unit = {
      stack.push((tpeMap, funMap))
      tpeMap = tpeMap.clone
      funMap = funMap.clone
    }

    def pop(): Unit = {
      val (ptpeMap, pfunMap) = stack.pop()
      tpeMap = ptpeMap
      funMap = pfunMap
    }

    def +=(p: (Set[Encoded], Matcher)): Unit = matcherKey(p._2.caller, p._2.tpe) match {
      case TypeKey(tpe) => tpeMap(tpe) = tpeMap.getOrElse(tpe, new Context) + p
      case key => funMap(key) = funMap.getOrElse(key, new Context) + p
    }

    def merge(that: ContextMap): this.type = {
      for ((tpe, values) <- that.tpeMap) tpeMap(tpe) = tpeMap.getOrElse(tpe, new Context) ++ values
      for ((caller, values) <- that.funMap) funMap(caller) = funMap.getOrElse(caller, new Context) ++ values
      this
    }

    def get(caller: Encoded, tpe: Type): Context =
      funMap.getOrElse(matcherKey(caller, tpe), new Context) ++ tpeMap.getOrElse(tpe, new Context)

    def get(key: MatcherKey): Context = key match {
      case TypeKey(tpe) => tpeMap.getOrElse(tpe, new Context)
      case key => funMap.getOrElse(key, new Context) ++ tpeMap.getOrElse(key.tpe, new Context)
    }

    def instantiations: Map[MatcherKey, MatcherSet] =
      (funMap.toMap ++ tpeMap.map { case (tpe,ms) => TypeKey(tpe) -> ms }).mapValues(_.toMatchers)
  }

  private class InstantiationContext private (
    private var _instantiated : Context, val map : ContextMap
  ) extends IncrementalState {

    private val stack = new MutableStack[Context]

    def this() = this(new Context, new ContextMap)

    def clear(): Unit = {
      stack.clear()
      map.clear()
      _instantiated = new Context
    }

    def reset(): Unit = clear()

    def push(): Unit = {
      stack.push(_instantiated)
      map.push()
    }

    def pop(): Unit = {
      _instantiated = stack.pop()
      map.pop()
    }

    def instantiated: Context = _instantiated
    def apply(p: (Set[Encoded], Matcher)): Boolean = _instantiated(p)

    def corresponding(m: Matcher): Context = map.get(m.caller, m.tpe)

    def instantiate(blockers: Set[Encoded], matcher: Matcher)(qs: MatcherQuantification*): Clauses = {
      if (this(blockers -> matcher)) {
        Seq.empty
      } else {
        map += (blockers -> matcher)
        _instantiated += (blockers -> matcher)
        qs.flatMap(_.instantiate(blockers, matcher))
      }
    }

    def merge(that: InstantiationContext): this.type = {
      _instantiated ++= that._instantiated
      map.merge(that.map)
      this
    }
  }

  private[solvers] trait MatcherQuantification {
    val pathVar: (Variable, Encoded)
    val quantifiers: Seq[(Variable, Encoded)]
    val matchers: Set[Matcher]
    val allMatchers: Matchers
    val condVars: Map[Variable, Encoded]
    val exprVars: Map[Variable, Encoded]
    val condTree: Map[Variable, Set[Variable]]
    val clauses: Clauses
    val blockers: Calls
    val applications: Apps
    val lambdas: Seq[LambdaTemplate]

    val holds: Encoded
    val body: Expr

    lazy val quantified: Set[Encoded] = quantifiers.map(_._2).toSet
    lazy val start = pathVar._2

    private lazy val depth = matchers.map(maxDepth).max
    private lazy val transMatchers: Set[Matcher] = (for {
      (b, ms) <- allMatchers.toSeq
      m <- ms if !matchers(m) && maxDepth(m) <= depth
    } yield m).toSet

    /* Build a mapping from applications in the quantified statement to all potential concrete
     * applications previously encountered. Also make sure the current `app` is in the mapping
     * as other instantiations have been performed previously when the associated applications
     * were first encountered.
     */
    private def mappings(bs: Set[Encoded], matcher: Matcher): Set[Set[(Set[Encoded], Matcher, Matcher)]] = {
      /* 1. select an application in the quantified proposition for which the current app can
       *    be bound when generating the new constraints
       */
      matchers.filter(qm => correspond(qm, matcher))

      /* 2. build the instantiation mapping associated to the chosen current application binding */
        .flatMap { bindingMatcher =>

      /* 2.1. select all potential matches for each quantified application */
          val matcherToInstances = matchers
            .map(qm => if (qm == bindingMatcher) {
              bindingMatcher -> Set(bs -> matcher)
            } else {
              qm -> instCtx.corresponding(qm)
            }).toMap

      /* 2.2. based on the possible bindings for each quantified application, build a set of
       *      instantiation mappings that can be used to instantiate all necessary constraints
       */
          val allMappings = matcherToInstances.foldLeft[Set[Set[(Set[Encoded], Matcher, Matcher)]]](Set(Set.empty)) {
            case (mappings, (qm, instances)) => Set(instances.toSeq.flatMap {
              case (bs, m) => mappings.map(mapping => mapping + ((bs, qm, m)))
            } : _*)
          }

          allMappings
        }
    }

    private def extractSubst(mapping: Set[(Set[Encoded], Matcher, Matcher)]): (Set[Encoded], Map[Encoded,Arg], Boolean) = {
      var constraints: Set[Encoded] = Set.empty
      var eqConstraints: Set[(Encoded, Encoded)] = Set.empty
      var subst: Map[Encoded, Arg] = Map.empty

      var matcherEqs: Set[(Encoded, Encoded)] = Set.empty
      def strictnessCnstr(qarg: Arg, arg: Arg): Unit = (qarg, arg) match {
        case (Right(qam), Right(am)) => (qam.args zip am.args).foreach(p => strictnessCnstr(p._1, p._2))
        case _ => matcherEqs += qarg.encoded -> arg.encoded
      }

      for {
        (bs, qm @ Matcher(qcaller, _, qargs, _), m @ Matcher(caller, _, args, _)) <- mapping
        _ = constraints ++= bs
        (qarg, arg) <- (qargs zip args)
        _ = strictnessCnstr(qarg, arg)
      } qarg match {
        case Left(quant) if !quantified(quant) || subst.isDefinedAt(quant) =>
          eqConstraints += (quant -> arg.encoded)
        case Left(quant) if quantified(quant) =>
          subst += quant -> arg
        case Right(qam) =>
          eqConstraints += (qam.encoded -> arg.encoded)
      }

      val substituter = mkSubstituter(subst.mapValues(_.encoded))
      val substConstraints = constraints.filter(_ != trueT).map(substituter)
      val substEqs = eqConstraints.map(p => substituter(p._1) -> p._2)
        .filter(p => p._1 != p._2).map(p => mkEquals(p._1, p._2))
      val enablers = substConstraints ++ substEqs
      val isStrict = matcherEqs.forall(p => substituter(p._1) == p._2)

      (enablers, subst, isStrict)
    }

    def instantiate(bs: Set[Encoded], matcher: Matcher): Clauses = {
      var clauses: Clauses = Seq.empty

      for (mapping <- mappings(bs, matcher)) {
        val (enablers, subst, isStrict) = extractSubst(mapping)

        if (!skip(subst)) {
          if (!isStrict) {
            val msubst = subst.collect { case (c, Right(m)) => c -> m }
            val substituter = mkSubstituter(subst.mapValues(_.encoded))
            ignoredSubsts(this) += ((currentGen + 3, enablers, subst))
          } else {
            clauses ++= instantiateSubst(enablers, subst, strict = true)
          }
        }
      }

      clauses
    }

    def instantiateSubst(enablers: Set[Encoded], subst: Map[Encoded, Arg], strict: Boolean = false): Clauses = {
      if (handledSubsts(this)(enablers -> subst)) {
        Seq.empty
      } else {
        handledSubsts(this) += enablers -> subst

        var clauses: Clauses = Seq.empty
        val (enabler, optEnabler) = freshBlocker(enablers)
        if (optEnabler.isDefined) {
          clauses :+= mkEquals(enabler, optEnabler.get)
        }

        val baseSubst = subst ++ instanceSubst(enabler).mapValues(Left(_))
        val (substMap, cls) = Template.substitution(
          condVars, exprVars, condTree, lambdas, Seq.empty, baseSubst, pathVar._1, enabler)
        clauses ++= cls

        val msubst = substMap.collect { case (c, Right(m)) => c -> m }
        val substituter = mkSubstituter(substMap.mapValues(_.encoded))
        registerBlockers(substituter)

        clauses ++= Template.instantiate(clauses, blockers, applications, Map.empty, substMap)

        for ((b,ms) <- allMatchers; m <- ms) {
          val sb = enablers ++ (if (b == start) Set.empty else Set(substituter(b)))
          val sm = m.substitute(substituter, msubst)

          if (strict && (matchers(m) || transMatchers(m))) {
            clauses ++= instCtx.instantiate(sb, sm)(quantifications.toSeq : _*)
          } else if (!matchers(m)) {
            ignoredMatchers += ((currentGen + 2 + totalDepth(m), sb, sm))
          }
        }

        clauses
      }
    }

    protected def instanceSubst(enabler: Encoded): Map[Encoded, Encoded]

    protected def skip(subst: Map[Encoded, Arg]): Boolean = false

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

  private class Quantification (
    val pathVar: (Variable, Encoded),
    val qs: (Variable, Encoded),
    val q2s: (Variable, Encoded),
    val insts: (Variable, Encoded),
    val guardVar: Encoded,
    val quantifiers: Seq[(Variable, Encoded)],
    val matchers: Set[Matcher],
    val allMatchers: Matchers,
    val condVars: Map[Variable, Encoded],
    val exprVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: Calls,
    val applications: Apps,
    val lambdas: Seq[LambdaTemplate],
    val template: QuantificationTemplate) extends MatcherQuantification {

    private var _currentQ2Var: Encoded = qs._2
    def currentQ2Var = _currentQ2Var
    val holds = qs._2
    val body = template.forall.body

    private var _insts: Map[Encoded, Set[Encoded]] = Map.empty
    def instantiations = _insts

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

  private lazy val blockerSymbol = Variable(FreshIdentifier("blocker", true), BooleanType)
  private lazy val enablersToBlocker: MutableMap[Set[Encoded], Encoded] = MutableMap.empty
  private lazy val blockerToEnablers: MutableMap[Encoded, Set[Encoded]] = MutableMap.empty
  private def freshBlocker(enablers: Set[Encoded]): (Encoded, Option[Encoded]) = enablers.toSeq match {
    case Seq(b) if isBlocker(b) => (b, None)
    case _ =>
      val last = enablersToBlocker.get(enablers).orElse {
        val initialEnablers = enablers.flatMap(e => blockerToEnablers.getOrElse(e, Set(e)))
        enablersToBlocker.get(initialEnablers)
      }

      last match {
        case Some(b) => (b, None)
        case None =>
          val nb = encodeSymbol(blockerSymbol)
          enablersToBlocker += enablers -> nb
          blockerToEnablers += nb -> enablers
          for (b <- enablers if isBlocker(b)) impliesBlocker(b, nb)
          blocker(nb)

          (nb, Some(encodeEnablers(enablers)))
      }
  }

  private class LambdaAxiom (
    val pathVar: (Variable, Encoded),
    val blocker: Encoded,
    val guardVar: Encoded,
    val quantifiers: Seq[(Variable, Encoded)],
    val matchers: Set[Matcher],
    val allMatchers: Map[Encoded, Set[Matcher]],
    val condVars: Map[Variable, Encoded],
    val exprVars: Map[Variable, Encoded],
    val condTree: Map[Variable, Set[Variable]],
    val clauses: Clauses,
    val blockers: Calls,
    val applications: Apps,
    val lambdas: Seq[LambdaTemplate],
    val template: LambdaTemplate) extends MatcherQuantification {

    val holds = start
    val body = template.lambda.body

    protected def instanceSubst(enabler: Encoded): Map[Encoded, Encoded] = {
      Map(guardVar -> start, blocker -> enabler)
    }

    override protected def skip(subst: Map[Encoded, Arg]): Boolean = {
      val substituter = mkSubstituter(subst.mapValues(_.encoded))
      val msubst = subst.collect { case (c, Right(m)) => c -> m }
      allMatchers.forall { case (b, ms) =>
        ms.forall(m => matchers(m) || instCtx(Set(substituter(b)) -> m.substitute(substituter, msubst)))
      }
    }
  }

  private def extractQuorums(
    quantified: Set[Encoded],
    matchers: Set[Matcher],
    lambdas: Seq[LambdaTemplate]
  ): Seq[Set[Matcher]] = {
    val extMatchers: Set[Matcher] = {
      def rec(templates: Seq[LambdaTemplate]): Set[Matcher] =
        templates.foldLeft(Set.empty[Matcher]) {
          case (matchers, template) => matchers ++ template.matchers.flatMap(_._2) ++ rec(template.lambdas)
        }

      matchers ++ rec(lambdas)
    }

    val quantifiedMatchers = for {
      m @ Matcher(_, _, args, _) <- extMatchers
      if args exists (_.left.exists(quantified))
    } yield m

    extractQuorums(quantifiedMatchers, quantified,
      (m: Matcher) => m.args.collect { case Right(m) if quantifiedMatchers(m) => m }.toSet,
      (m: Matcher) => m.args.collect { case Left(a) if quantified(a) => a }.toSet)
  }

  def instantiateAxiom(template: LambdaTemplate, substMap: Map[Encoded, Arg]): Clauses = {
    def quantifiedMatcher(m: Matcher): Boolean = m.args.exists(a => a match {
      case Left(v) => isQuantifier(v)
      case Right(m) => quantifiedMatcher(m)
    })

    val quantified = template.arguments flatMap {
      case (id, idT) => substMap(idT) match {
        case Left(v) if isQuantifier(v) => Some(id)
        case Right(m) if quantifiedMatcher(m) => Some(id)
        case _ => None
      }
    }

    val quantifiers = quantified zip abstractNormalizer.normalize(quantified)
    val key = template.structure -> quantifiers

    if (quantifiers.isEmpty || lambdaAxioms(key)) {
      Seq.empty
    } else {
      lambdaAxioms += key
      val blockerT = encodeSymbol(blockerSymbol)

      val guard = Variable(FreshIdentifier("guard", true), BooleanType)
      val guardT = encodeSymbol(guard)

      val substituter = mkSubstituter(substMap.mapValues(_.encoded) + (template.start -> blockerT))
      val msubst = substMap.collect { case (c, Right(m)) => c -> m }

      val allMatchers = template.matchers map { case (b, ms) =>
        substituter(b) -> ms.map(_.substitute(substituter, msubst))
      }

      val qMatchers = allMatchers.flatMap(_._2).toSet

      val encArgs = template.args map (arg => Left(arg).substitute(substituter, msubst))
      val app = Application(template.ids._1, template.arguments.map(_._1))
      val appT = encodeExpr((template.arguments.map(_._1) zip encArgs.map(_.encoded)).toMap + template.ids)(app)
      val selfMatcher = Matcher(template.ids._2, template.tpe, encArgs, appT)

      val instMatchers = allMatchers + (template.start -> (allMatchers.getOrElse(template.start, Set.empty) + selfMatcher))

      val enablingClause = mkImplies(guardT, blockerT)

      val condVars = template.condVars map { case (id, idT) => id -> substituter(idT) }
      val exprVars = template.exprVars map { case (id, idT) => id -> substituter(idT) }
      val clauses = (template.clauses map substituter) :+ enablingClause
      val blockers = template.blockers map { case (b, fis) =>
        substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(_.substitute(substituter, msubst))))
      }

      val applications = template.applications map { case (b, apps) =>
        substituter(b) -> apps.map(app => app.copy(
          caller = substituter(app.caller),
          args = app.args.map(_.substitute(substituter, msubst))
        ))
      }

      val lambdas = template.lambdas map (_.substitute(substituter, msubst))

      val quantified = quantifiers.map(_._2).toSet
      val matchQuorums = extractQuorums(quantified, qMatchers, lambdas)

      var instantiation: Clauses = Seq.empty

      for (matchers <- matchQuorums) {
        val axiom = new LambdaAxiom(template.pathVar._1 -> substituter(template.start),
          blockerT, guardT, quantifiers, matchers, instMatchers, condVars, exprVars, template.condTree,
          clauses, blockers, applications, lambdas, template)

        quantifications += axiom
        handledSubsts += axiom -> MutableSet.empty
        ignoredSubsts += axiom -> MutableSet.empty

        val newCtx = new InstantiationContext()
        for ((b,m) <- instCtx.instantiated) {
          instantiation ++= newCtx.instantiate(b, m)(axiom)
        }
        instCtx.merge(newCtx)
      }

      instantiation ++= instantiateConstants(quantifiers, qMatchers)

      instantiation
    }
  }

  def instantiateQuantification(template: QuantificationTemplate): (Encoded, Clauses) = {
    templates.get(template.key) match {
      case Some(idT) =>
        (idT, Seq.empty)

      case None =>
        val qT = encodeSymbol(template.qs._1)
        val quantified = template.quantifiers.map(_._2).toSet
        val matcherSet = template.matchers.flatMap(_._2).toSet
        val matchQuorums = extractQuorums(quantified, matcherSet, template.lambdas)

        var clauses: Clauses = Seq.empty

        val qs = for (matchers <- matchQuorums) yield {
          val newQ = encodeSymbol(template.qs._1)
          val substituter = mkSubstituter(Map(template.qs._2 -> newQ))

          val quantification = new Quantification(
            template.pathVar,
            template.qs._1 -> newQ,
            template.q2s, template.insts, template.guardVar,
            template.quantifiers, matchers, template.matchers,
            template.condVars, template.exprVars, template.condTree,
            template.clauses map substituter, // one clause depends on 'q' (and therefore 'newQ')
            template.blockers, template.applications, template.lambdas, template)

          quantifications += quantification
          handledSubsts += quantification -> MutableSet.empty
          ignoredSubsts += quantification -> MutableSet.empty

          val newCtx = new InstantiationContext()
          for ((b,m) <- instCtx.instantiated) {
            clauses ++= newCtx.instantiate(b, m)(quantification)
          }
          instCtx.merge(newCtx)

          quantification.qs._2
        }

        clauses :+= {
          val newQs =
            if (qs.isEmpty) trueT
            else if (qs.size == 1) qs.head
            else mkAnd(qs : _*)
          mkImplies(template.start, mkEquals(qT, newQs))
        }

        clauses ++= instantiateConstants(template.quantifiers, matcherSet)

        templates += template.key -> qT
        (qT, clauses)
    }
  }

  def instantiateMatcher(blocker: Encoded, matcher: Matcher): Clauses = {
    instCtx.instantiate(Set(blocker), matcher)(quantifications.toSeq : _*)
  }

  def canUnfoldQuantifiers: Boolean = ignoredSubsts.nonEmpty || ignoredMatchers.nonEmpty

  def instantiateIgnored(force: Boolean = false): Clauses = {
    currentGen = if (!force) currentGen + 1 else {
      val gens = ignoredSubsts.toSeq.flatMap(_._2).map(_._1) ++ ignoredMatchers.toSeq.map(_._1)
      if (gens.isEmpty) currentGen else gens.min
    }

    var clauses: Clauses = Seq.empty

    val matchersToRelease = ignoredMatchers.toList.flatMap { case e @ (gen, b, m) =>
      if (gen == currentGen) {
        ignoredMatchers -= e
        Some(b -> m)
      } else {
        None
      }
    }

    for ((bs,m) <- matchersToRelease) {
      clauses ++= instCtx.instantiate(bs, m)(quantifications.toSeq : _*)
    }

    val substsToRelease = quantifications.toList.flatMap { q =>
      val qsubsts = ignoredSubsts(q)
      qsubsts.toList.flatMap { case e @ (gen, enablers, subst) =>
        if (gen == currentGen) {
          qsubsts -= e
          Some((q, enablers, subst))
        } else {
          None
        }
      }
    }

    for ((q, enablers, subst) <- substsToRelease) {
      clauses ++= q.instantiateSubst(enablers, subst, strict = false)
    }

    clauses
  }

  private def instantiateConstants(quantifiers: Seq[(Variable, Encoded)], matchers: Set[Matcher]): Clauses = {
    var clauses: Clauses = Seq.empty

    for (normalizer <- List(abstractNormalizer, concreteNormalizer)) {
      val quantifierSubst = normalizer.normalSubst(quantifiers)
      val substituter = mkSubstituter(quantifierSubst)

      for {
        m <- matchers
        sm = m.substitute(substituter, Map.empty)
        if !instCtx.corresponding(sm).exists(_._2.args == sm.args)
      } clauses ++= instCtx.instantiate(Set.empty, sm)(quantifications.toSeq : _*)

      def unifyMatchers(matchers: Seq[Matcher]): Clauses = matchers match {
        case sm +: others =>
          var clauses: Clauses = Seq.empty
          for (pm <- others if correspond(pm, sm)) {
            val encodedArgs = (sm.args zip pm.args).map(p => p._1.encoded -> p._2.encoded)
            val mismatches = encodedArgs.zipWithIndex.collect {
              case ((sa, pa), idx) if isQuantifier(sa) && isQuantifier(pa) && sa != pa => (idx, (pa, sa))
            }.toMap

            def extractChains(indexes: Seq[Int], partials: Seq[Seq[Int]]): Seq[Seq[Int]] = indexes match {
              case idx +: xs =>
                val (p1, p2) = mismatches(idx)
                val newPartials = Seq(idx) +: partials.map { seq =>
                  if (mismatches(seq.head)._1 == p2) idx +: seq
                  else if (mismatches(seq.last)._2 == p1) seq :+ idx
                  else seq
                }

                val (closed, remaining) = newPartials.partition { seq =>
                  mismatches(seq.head)._1 == mismatches(seq.last)._2
                }
                closed ++ extractChains(xs, partials ++ remaining)

              case _ => Seq.empty
            }

            val chains = extractChains(mismatches.keys.toSeq, Seq.empty)
            val positions = chains.foldLeft(Map.empty[Int, Int]) { (mapping, seq) =>
              val res = seq.min
              mapping ++ seq.map(i => i -> res)
            }

            def extractArgs(args: Seq[Arg]): Seq[Arg] =
              (0 until args.size).map(i => args(positions.getOrElse(i, i)))

            clauses ++= instCtx.instantiate(Set.empty, sm.copy(args = extractArgs(sm.args)))(quantifications.toSeq : _*)
            clauses ++= instCtx.instantiate(Set.empty, pm.copy(args = extractArgs(pm.args)))(quantifications.toSeq : _*)
          }

          clauses ++ unifyMatchers(others)

        case _ => Seq.empty
      }

      if (normalizer == abstractNormalizer) {
        val substMatchers = matchers.map(_.substitute(substituter, Map.empty))
        clauses ++= unifyMatchers(substMatchers.toSeq)
      }
    }

    clauses
  }

  def getFiniteRangeClauses: Clauses = {
    val clauses = new scala.collection.mutable.ListBuffer[Encoded]
    val keyClause = MutableMap.empty[MatcherKey, (Clauses, Encoded)]

    for ((_, bs, m) <- ignoredMatchers) {
      val key = matcherKey(m.caller, m.tpe)
      val QuantificationTypeMatcher(argTypes, _) = key.tpe

      val (values, clause) = keyClause.getOrElse(key, {
        val insts = instCtx.map.get(key).toMatchers

        val guard = Variable(FreshIdentifier("guard", true), BooleanType)
        val elems = argTypes.map(tpe => Variable(FreshIdentifier("elem", true), tpe))
        val values = argTypes.map(tpe => Variable(FreshIdentifier("value", true), tpe))
        val expr = andJoin(guard +: (elems zip values).map(p => Equals(p._1, p._2)))

        val guardP = guard -> encodeSymbol(guard)
        val elemsP = elems.map(e => e -> encodeSymbol(e))
        val valuesP = values.map(v => v -> encodeSymbol(v))
        val exprT = encodeExpr(elemsP.toMap ++ valuesP + guardP)(expr)

        val disjuncts = insts.toSeq.map { case (b, im) =>
          val bp = if (m.caller != im.caller) mkAnd(mkEquals(m.caller, im.caller), b) else b
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
      val exprT = encodeExpr(elemsP.toMap ++ valuesP + guardP)(expr)

      val disjunction = handledSubsts(q) match {
        case set if set.isEmpty => encodeExpr(Map.empty)(BooleanLiteral(false))
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

    def isQuantified(e: Arg): Boolean = e match {
      case Left(t) => isQuantifier(t)
      case Right(m) => m.args.exists(isQuantified)
    }

    for ((key, ctx) <- instCtx.map.instantiations) {
      val QuantificationTypeMatcher(argTypes, _) = key.tpe

      for {
        (tpe, idx) <- argTypes.zipWithIndex
        quants <- abstractNormalizer.get(tpe) if quants.nonEmpty
        (b, m) <- ctx
        arg = m.args(idx) if !isQuantified(arg)
      } clauses += mkAnd(quants.map(q => mkNot(mkEquals(q, arg.encoded))) : _*)

      val byPosition: Iterable[Seq[Encoded]] = ctx.flatMap { case (b, m) =>
        if (b != trueT) Seq.empty else m.args.zipWithIndex
      }.groupBy(_._2).map(p => p._2.toSeq.flatMap {
        case (a, _) => if (isQuantified(a)) Some(a.encoded) else None
      }).filter(_.nonEmpty)

      for ((a +: as) <- byPosition; a2 <- as) {
        clauses += mkEquals(a, a2)
      }
    }

    clauses.toSeq
  }

  trait ModelView {
    protected val vars: Map[Variable, Encoded]
    protected val evaluator: evaluators.DeterministicEvaluator

    protected def get(id: Variable): Option[Expr]
    protected def eval(elem: Encoded, tpe: Type): Option[Expr]

    implicit lazy val context = evaluator.context
    lazy val reporter = context.reporter

    private def extract(b: Encoded, m: Matcher): Option[Seq[Expr]] = {
      val QuantificationTypeMatcher(fromTypes, _) = m.tpe
      val optEnabler = eval(b, BooleanType)
      optEnabler.filter(_ == BooleanLiteral(true)).flatMap { _ =>
        val optArgs = (m.args zip fromTypes).map { case (arg, tpe) => eval(arg.encoded, tpe) }
        if (optArgs.forall(_.isDefined)) Some(optArgs.map(_.get))
        else None
      }
    }

    private def functionsOf(expr: Expr, path: Expr): (Seq[(Expr, Expr)], Seq[Expr] => Expr) = {

      def reconstruct(subs: Seq[(Seq[(Expr, Expr)], Seq[Expr] => Expr)],
                      recons: Seq[Expr] => Expr): (Seq[(Expr, Expr)], Seq[Expr] => Expr) =
        (subs.flatMap(_._1), (exprs: Seq[Expr]) => {
          var curr = exprs
          recons(subs.map { case (es, recons) =>
            val (used, remaining) = curr.splitAt(es.size)
            curr = remaining
            recons(used)
          })
        })

      def rec(expr: Expr, path: Expr): (Seq[(Expr, Expr)], Seq[Expr] => Expr) = expr match {
        case (_: Lambda) =>
          (Seq(expr -> path), (es: Seq[Expr]) => es.head)

        case Tuple(es) => reconstruct(es.zipWithIndex.map {
          case (e, i) => rec(e, TupleSelect(path, i + 1))
        }, Tuple)

        case CaseClass(cct, es) => reconstruct((cct.classDef.fieldsIds zip es).map {
          case (id, e) => rec(e, CaseClassSelector(cct, path, id))
        }, CaseClass(cct, _))

        case _ => (Seq.empty, (es: Seq[Expr]) => expr)
      }

      rec(expr, path)
    }

    def getTotalModel: Model = {

      def checkForalls(quantified: Set[Variable], body: Expr): Option[String] = {
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

          case Operator(es, _) if (es.flatMap(variablesOf).toSet & quantified).nonEmpty =>
            return Some("Unandled implications from operation " + m.asString)

          case _ =>
        }) (body)

        body match {
          case v: Variable if quantified(v) =>
            Some("Unexpected free quantifier " + id.asString)
          case _ => None
        }
      }

      val issues: Iterable[(Seq[Variable], Expr, String)] = for {
        q <- quantifications.view
        if eval(q.holds, BooleanType) == Some(BooleanLiteral(true))
        msg <- checkForalls(q.quantifiers.map(_._1).toSet, q.body)
      } yield (q.quantifiers.map(_._1), q.body, msg)

      if (issues.nonEmpty) {
        val (quantifiers, body, msg) = issues.head
        reporter.warning("Model soundness not guaranteed for \u2200" +
          quantifiers.map(_.asString).mkString(",") + ". " + body.asString+" :\n => " + msg)
      }

      val types = typeInstantiations
      val partials = partialInstantiations

      def extractCond(params: Seq[Variable], args: Seq[(Encoded, Expr)], structure: Map[Encoded, Variable]): Seq[Expr] = (params, args) match {
        case (id +: rparams, (v, arg) +: rargs) =>
          if (isQuantifier(v)) {
            structure.get(v) match {
              case Some(pid) => Equals(id, pid) +: extractCond(rparams, rargs, structure)
              case None => extractCond(rparams, rargs, structure + (v -> id))
            }
          } else {
            Equals(id, arg) +: extractCond(rparams, rargs, structure)
          }
        case _ => Seq.empty
      }

      new Model(vars.map { case (id, idT) =>
        val value = get(id).getOrElse(simplestValue(id.getType))
        val (functions, recons) = functionsOf(value, id)

        id -> recons(functions.map { case (f, path) =>
          val encoded = encodeExpr(Map(id -> idT))(path)
          val tpe = bestRealType(f.getType).asInstanceOf[FunctionType]
          val params = tpe.from.map(tpe => Variable(FreshIdentifier("x", true), tpe))
          partials.get(encoded).orElse(types.get(tpe)).map { domain =>
            val conditionals = domain.flatMap { case (b, m) =>
              extract(b, m).map { args =>
                val result = evaluator.eval(application(f, args)).result.getOrElse {
                  scala.sys.error("Unexpectedly failed to evaluate " + application(f, args))
                }

                val cond = if (m.args.exists(arg => isQuantifier(arg.encoded))) {
                  extractCond(params, m.args.map(_.encoded) zip args, Map.empty)
                } else {
                  (params zip args).map(p => Equals(p._1, p._2))
                }

                cond -> result
              }
            }.toMap

            if (conditionals.isEmpty) f match {
              case FiniteLambda(mapping, dflt, tpe) =>
                Lambda(params.map(ValDef(_)), mapping.foldRight(dflt) { case ((es, v), elze) =>
                  IfExpr(andJoin((params zip es).map(p => Equals(p._1.toVariable, p._2))), v, elze)
                })
              case _ => f
            } else {
              val ((_, dflt)) +: rest = conditionals.toSeq.sortBy { case (conds, _) =>
                (conds.flatMap(variablesOf).toSet.size, conds.size)
              }

              val body = rest.foldLeft(dflt) { case (elze, (conds, res)) =>
                if (conds.isEmpty) elze else (elze match {
                  case pres if res == pres => res
                  case _ => IfExpr(andJoin(conds), res, elze)
                })
              }

              Lambda(params.map(_.toVal), body)
            }
          }.getOrElse(f)
        })
      })
    }
  }

  def getModel(vs: Map[Variable, Encoded], ev: DeterministicEvaluator, _get: Variable => Option[Expr], _eval: (Encoded, Type) => Option[Expr]) = new ModelView {
    val vars: Map[Variable, Encoded] = vs
    val evaluator: DeterministicEvaluator = ev

    def get(id: Variable): Option[Expr] = _get(id)
    def eval(elem: Encoded, tpe: Type): Option[Expr] = _eval(elem, tpe)
  }

  def getInstantiationsWithBlockers = quantifications.toSeq.flatMap {
    case q: Quantification => q.instantiations.toSeq
    case _ => Seq.empty
  }
}
