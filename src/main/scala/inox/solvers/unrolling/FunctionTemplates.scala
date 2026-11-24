/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.immutable.VectorMap
import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

trait FunctionTemplates { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import functionsManager._

  /** The caches of the function templates, which push and pop leave as they are. Each one maps its
    * key to a value that only depends on the key and the program, such as a template, or to a fresh
    * symbol that stands for the same thing wherever it is used, such as the rank function of a
    * function. The clauses that mention such a symbol may be popped, and the clauses asserted
    * later then constrain it anew. */
  private object functionCaches {
    /** The template of each function. */
    val templates: MutableMap[TypedFunDef, FunctionTemplate] = MutableMap.empty
    /** The template of the interpretation of each uninterpreted function (see [[InterpretedTemplate]]). */
    val interpreted: MutableMap[Interpreted, FunctionTemplate] = MutableMap.empty
    /** The rank function of each function, and its encoding (see [[rankClauses]]). */
    val ranks: MutableMap[TypedFunDef, Variable] = MutableMap.empty
    val rankSymbols: MutableMap[Variable, Encoded] = MutableMap.empty
    /** Whether calls of each function can reach an uninterpreted function (see [[callsUninterpreted]]). */
    val uninterpreted: MutableMap[Identifier, Boolean] = MutableMap.empty
    /** The encoding of a call of each function, on fresh arguments (see [[mkCall]]). */
    val calls: MutableMap[TypedFunDef, (Seq[Encoded], Encoded)] = MutableMap.empty
    /** The negation of each blocker of calls (see [[functionsManager.satisfactionAssumptions]]). */
    val negations: MutableMap[Encoded, Encoded] = MutableMap.empty
    /** Whether `diverges` was created, after which the search for models assumes it doesn't hold. */
    var rankedCalls = false
  }

  protected def variableSeq(tpe: Type): Seq[Variable] = {
    val free = typeOps.variablesOf(tpe)
    val vars = new scala.collection.mutable.ListBuffer[Variable]

    new ConcreteSelfTreeTraverser {
      override def traverse(e: Expr): Unit = e match {
        case v: Variable if free(v) => vars += v
        case _ => super.traverse(e)
      }
    }.traverse(tpe)
    vars.toSeq.distinct
  }

  object FunctionTemplate {
    def apply(tfd: TypedFunDef): FunctionTemplate = functionCaches.templates.getOrElse(tfd, {
      val body: Expr = timers.solvers.simplify.run { simplifyFormula(tfd.fullBody) }

      val tpVars = tfd.tps.flatMap(variableSeq).distinct
      val fdArgs: Seq[Variable] = tfd.params.map(_.toVariable)
      val call: Expr = tfd.applied(fdArgs)

      val start = Variable.fresh("start", BooleanType(), true)
      val pathVar = start -> encodeSymbol(start)
      val arguments = (fdArgs ++ tpVars).map(v => v -> encodeSymbol(v))
      val substMap = arguments.toMap + pathVar

      val (p, bodyClauses) = mkExprClauses(start, body, substMap)

      // The calls that evaluating the body reaches, with the blockers of their paths (see `rankClauses`)
      val bodySites: Seq[(Variable, FunctionInvocation)] = {
        def invocations(e: Expr): Seq[FunctionInvocation] = exprOps.collectPreorder[FunctionInvocation] {
          case fi: FunctionInvocation => Seq(fi)
          case _ => Seq.empty
        } (e)
        ((bodyClauses.guardedExprs `merge` bodyClauses.definitions).toSeq.flatMap { case (b, es) => es.flatMap(invocations).map(b -> _) } ++
          invocations(p).map(start -> _)).distinct
      }

      val tmplClauses: TemplateClauses = {
        val clauses = bodyClauses + (start -> Equals(call, p))

        // Register the function's return as a contract typing to enable
        // induction with refinement types
        if (ContractUnrolling `unroll` tfd.returnType) {
          // The return type only holds for arguments that lie in the parameter types, so
          // it is assumed only once the arguments' membership in these types is shown.
          // Under `optAssumeChecked`, the front-end has checked the arguments of every call, so
          // the return type is assumed directly.
          val (domains, domClauses) = if (modes.assumeChecked) (Seq.empty[Expr], TemplateClauses()) else
            tfd.params.foldLeft((Seq.empty[Expr], TemplateClauses())) { case ((domains, domClauses), vd) =>
              mkTypeClauses(start, vd.tpe, vd.toVariable, substMap, inDomain = true)(using MembershipGenerator) match {
                case (BooleanLiteral(true), _) => (domains, domClauses)
                case (p, pClauses) => (domains :+ p, domClauses ++ pClauses)
              }
            }

          val allClauses = clauses ++ domClauses
          val closures = typeOps.variablesOf(tfd.returnType).toSeq.sortBy(_.id).map(v => Left(substMap(v)))
          val call = mkCall(tfd, arguments.map(_._2))
          if (domains.isEmpty) {
            val typing = Typing(tfd.returnType, call, Constraint(trueT, closures, false))
            allClauses.copy(types = allClauses.types `merge` Map(pathVar._2 -> Set(typing)))
          } else {
            val result = Variable.fresh("result", BooleanType(), true)
            val resultT = encodeSymbol(result)
            val typing = Typing(tfd.returnType, call, Constraint(resultT, closures, false))
            allClauses.copy(
              exprVars = allClauses.exprVars + (result -> resultT),
              guardedExprs = allClauses.guardedExprs `merge` (start -> Implies(andJoin(domains), result)),
              types = allClauses.types `merge` Map(pathVar._2 -> Set(typing)))
          }
        } else {
          clauses
        }
      }

      val (contents0, str) = Template.contents(
        pathVar, arguments, tmplClauses, optCall = Some(Defined(tfd)), partial = true)
      val contents = contents0.copy(
        clauses = contents0.clauses ++ rankClauses(tfd, contents0, bodySites),
        source = templateSource(substMap, Some(call), body))

      val funString : () => String = () => {
        "Template for def " + tfd.signature +
        "(" + tfd.params.map(a => a.id.toString + " : " + a.getType).mkString(", ") + ") : " +
        tfd.getType + " is :\n" + str()
      }

      val res = new FunctionTemplate(contents, funString)
      functionCaches.templates(tfd) = res
      res
    })
  }

  /** Whether some call may reach itself on the same arguments (see `rankClauses`). The search for
    * models assumes that it doesn't, and proofs don't, so neither relies on a call diverging. */
  private lazy val diverges: Encoded = {
    functionCaches.rankedCalls = true
    encodeSymbol(Variable.fresh("diverges", BooleanType(), true))
  }

  /** The rank of the call `tfd(args)`: an uninterpreted integer function of the arguments. */
  private def rank(tfd: TypedFunDef, args: Seq[Expr]): Expr = {
    val r = functionCaches.ranks.getOrElseUpdate(tfd, {
      val r = Variable.fresh("rank_" + tfd.id.name,
        if (tfd.params.isEmpty) IntegerType() else FunctionType(tfd.params.map(_.getType), IntegerType()), true)
      functionCaches.rankSymbols(r) = encodeSymbol(r)
      r
    })
    if (tfd.params.isEmpty) r else Application(r, args)
  }

  /** Clauses stating that a call ranks higher than the calls that evaluating its body reaches, on the
    * paths that reach them.
    *
    * A call that returns a value has a finite evaluation, so ranking each call by the depth of its
    * evaluation satisfies these clauses. A call that reaches itself, possibly through other calls,
    * on the same arguments never returns, as evaluation is deterministic: the ranks along the cycle
    * can't decrease. Without these clauses, the equations of the calls on such a cycle, e.g.
    * `f(x) = g(x)` and `g(x) = f(x)`, would be satisfied by any value once every call on it is
    * unfolded, and models could rely on these values. This includes `f(x) = f(x)` for
    * `def f(x) = f(x)`, whose body call is dropped from the template (see `Template.extractCalls`).
    *
    * The clauses only hold unless `diverges` does, which the search for models assumes not to hold,
    * so that models never take the paths that close a cycle, but proofs don't: a query whose answer
    * depends on a call diverging is neither satisfiable nor refuted, as the evaluator can't tell
    * either, and the solver answers `Unknown`.
    *
    * Under `optAssumeChecked`, the front-end has checked that functions are total, so every call
    * returns and no call reaches itself: the clauses are satisfied by the depths of the evaluations,
    * whatever the values of the other symbols, and are left out.
    *
    * Only the calls of the body are ranked: the evaluator doesn't evaluate the calls in type checks,
    * and those in lambdas and quantifiers belong to their own templates.
    *
    * Among these, only the calls to the functions that call `tfd` back are ranked. A cycle of calls
    * stays among functions that call each other, so the clauses of the other calls don't rule out
    * any: given ranks that satisfy the clauses within each group of mutually recursive functions,
    * shifting the ranks of each group above those of the groups it calls satisfies them all, as
    * the clauses only mention finitely many calls. */
  private def rankClauses(tfd: TypedFunDef, contents: TemplateContents,
                          sites: Seq[(Variable, FunctionInvocation)]): Clauses = if (modes.assumeChecked) Seq.empty else {
    val callers = transitiveCallers(tfd.id)
    val ranked = sites.collect { case (b, fi) if callers(fi.id) => (b, fi, rank(fi.tfd, fi.args)) }
    if (ranked.isEmpty) Seq.empty else {
      val self = rank(tfd, tfd.params.map(_.toVariable))
      val allSymbols = Map(contents.pathVar) ++ contents.arguments ++ contents.condVars ++ contents.exprVars ++
        contents.lambdas.map(_.ids) ++ contents.quantifications.flatMap(_.mapping) ++ functionCaches.rankSymbols ++
        typeCaches.tpSubst ++ uninterpretedSubst
      val encoder = mkEncoder(allSymbols)
      ranked.flatMap { case (b, fi, callee) =>
        // Calls whose arguments mention symbols that the template doesn't bind aren't ranked
        if (!exprOps.variablesOf(callee).forall(allSymbols.contains)) Seq.empty
        else Rule.Decreases(encoder(b), encoder(GreaterThan(self, callee)), Some(diverges)).clauses
      }
    }
  }

  /** The templates of the interpretations of uninterpreted functions, whose calls are the
    * applications of their free functions (see [[TemplateGenerator.interpretedFunctions]]). */
  object InterpretedTemplate {
    def apply(callee: Interpreted): FunctionTemplate = functionCaches.interpreted.getOrElse(callee, {
      val Lambda(params, body) = interpretation(callee.id, callee.tps).get: @unchecked
      val args = params.map(_.freshen.toVariable)
      val interpreted = exprOps.replaceFromSymbols((params zip args).toMap, body)

      val start = Variable.fresh("start", BooleanType(), true)
      val pathVar = start -> encodeSymbol(start)
      val arguments = args.map(v => v -> encodeSymbol(v))
      val substMap = arguments.toMap + pathVar

      val (p, clauses) = mkExprClauses(start, interpreted, substMap)
      val tmplClauses = clauses + (start -> Equals(Application(callee.function, args), p))

      val (contents, str) = Template.contents(pathVar, arguments, tmplClauses, optCall = Some(callee), partial = true)
      val res = new FunctionTemplate(contents, () => "Template for the interpretation of " + callee.signature + " is :\n" + str())
      functionCaches.interpreted(callee) = res
      res
    })
  }

  class FunctionTemplate private[FunctionTemplates](
    val contents: TemplateContents,
    stringRepr: () => String) extends Template {

    private lazy val str : String = stringRepr()
    override def toString : String = str
  }

  def instantiateCall(blocker: Encoded, fi: Call): Clauses = {
    state.update(s => s.copy(calls = s.calls.register(blocker, nextGeneration(currentGeneration), Set(fi))))
    Seq.empty
  }

  def getCalls: Seq[(Encoded, Call)] = state.get.defBlockers.toList.map(p => p._2 -> p._1)

  /** Whether calls of `tfd` can reach an uninterpreted function, in which case ground calls of
    * `tfd` can't be evaluated. */
  private def callsUninterpreted(tfd: TypedFunDef): Boolean = functionCaches.uninterpreted.getOrElseUpdate(tfd.id,
    (transitiveCallees(tfd.fd) + tfd.fd).exists { fd =>
      exprOps.exists { case _: UninterpretedCall => true case _ => false } (fd.fullBody)
    })

  /** Records that the equality symbol of `tpe` is constrained on some terms, by an unfolded equality
    * or by the conclusion of a congruence, so that it can hold of distinct terms. */
  private[unrolling] def constrainEquality(tpe: Type): Unit =
    state.update(s => s.copy(constrained = s.constrained + tpe))

  /** The pairs of unfolded calls of a function that have no [[Rule.Congruence]] yet and for which it
    * can tell the solver something, with their blockers and the arguments on which they differ.
    *
    * The solver already knows that calls are functions of their arguments, so the rule only adds
    * to that when the calls differ on arguments whose type needs equality unrolling, and only once
    * the equality symbols of these types are constrained. The pairs are in the order in which the
    * calls were unfolded, so that the clauses don't depend on hash codes. */
  private def waitingCongruences: Iterator[(TypedFunDef, (Call, Encoded), (Call, Encoded), Seq[(Type, Encoded, Encoded)])] = {
    val constrained = state.get.constrained
    if (constrained.isEmpty) Iterator.empty else {
      val calls = state.get.defBlockers.toSeq.collect {
        case (call @ Call(Defined(tfd), _, _), blocker) if tfd.params.exists(vd => constrained(vd.getType)) => (tfd, call, blocker)
      }

      for {
        ((tfd, call1, blocker1), i) <- calls.iterator.zipWithIndex
        (_, call2, blocker2) <- calls.iterator.drop(i + 1)
        if call2.callee == call1.callee && !state.get.congruent(call1 -> call2)
        differing = (tfd.params zip (call1.args zip call2.args)).collect {
          case (vd, (e1, e2)) if e1.encoded != e2.encoded && unrollEquality(vd.getType) => (vd.getType, e1.encoded, e2.encoded)
        }
        if differing.nonEmpty && differing.forall(d => constrained(d._1))
      } yield (tfd, call1 -> blocker1, call2 -> blocker2, differing)
    }
  }

  /** Whether a model of a proof check can call for congruences (see [[modelCongruences]]). */
  protected def hasWaitingCongruences: Boolean = waitingCongruences.hasNext

  /** The [[Rule.Congruence]] of the pairs of unfolded calls that the model of a proof check reaches
    * and whose differing arguments it makes equal, where `holds` tells whether the model satisfies
    * a literal. Such a model breaks the congruence, or doesn't depend on it.
    *
    * Each pair of calls of a function on values with a custom equality (e.g. bags on Princess)
    * would otherwise get its own clauses, and formulas would grow quadratically with the number of
    * calls. The clauses only shortcut the unfolding of both calls, so their equalities are not
    * unrolled. */
  protected def modelCongruences(holds: Encoded => Boolean): Clauses = {
    val cache = MutableMap.empty[Encoded, Boolean]
    def cached(e: Encoded): Boolean = cache.getOrElseUpdate(e, holds(e))

    val pairs = waitingCongruences.filter { case (_, (_, blocker1), (_, blocker2), differing) =>
      cached(blocker1) && cached(blocker2) && differing.forall { case (tpe, e1, e2) => cached(equality(tpe, e1, e2)) }
    }.toSeq

    pairs.flatMap { case (tfd, (call1, blocker1), (call2, blocker2), _) =>
      state.update(s => s.copy(congruent = s.congruent + (call1 -> call2)))

      val (equalities, equalityClauses) = (tfd.params.map(_.getType) zip (call1.args zip call2.args)).map {
        case (tpe, (e1, e2)) => guardedEquality(blocker1, tpe, e1.encoded, e2.encoded)
      }.unzip

      val (entail, entailClauses) = guardedEquality(blocker1, tfd.getType,
        mkCall(tfd, call1.args.map(_.encoded)), mkCall(tfd, call2.args.map(_.encoded)))

      // the rule constrains the equality of the results
      if (unrollEquality(tfd.getType)) constrainEquality(tfd.getType)

      equalityClauses.flatten ++ entailClauses ++
        Rule.Congruence(blocker1 +: blocker2 +: equalities, entail).clauses
    }
  }

  /** The template of the call `tfd(args)` under `blocker`, as the value that the evaluator computed
    * for it. */
  private def valueTemplate(tfd: TypedFunDef, value: Expr, blocker: Encoded, args: Seq[Arg]): Template = {
    val start = Variable.fresh("cs", BooleanType())
    val (p, cls) = mkExprClauses(start, value, Map(start -> blocker))
    val tmplClauses = cls + (start -> Equals(tfd.applied, p))

    val (valueContents, _) = Template.contents(
      start -> blocker,
      tfd.params.map(_.toVariable) zip args.map(_.encoded),
      tmplClauses,
      optCall = Some(Defined(tfd)),
      partial = true
    )

    new Template { val contents = valueContents }
  }

  private[unrolling] def mkCall(tfd: TypedFunDef, args: Seq[Encoded]): Encoded = {
    val (asT, call) = functionCaches.calls.getOrElse(tfd, {
      val as = tfd.params.map(vd => Variable.fresh("x", vd.getType, true))
      val asT = as.map(encodeSymbol)
      val res = (asT, mkEncoder((as zip asT).toMap)(tfd.applied(as)))
      functionCaches.calls(tfd) = res
      res
    })

    mkSubstituter((asT zip args).toMap)(call)
  }

  /** The state of [[functionsManager]], which push saves and pop restores as a whole.
    *
    * @param calls the calls that each blocker guards, which are unfolded with it
    * @param defBlockers the definition blocker of each unfolded call, under which its body is
    *                    instantiated, in the order in which the calls were unfolded
    * @param constrained the types whose equality symbol is constrained (see [[constrainEquality]])
    * @param congruent the pairs of calls whose congruence was built (see [[modelCongruences]]), the
    *                  call that was unfolded first coming first */
  private[unrolling] case class FunctionsState(
    calls: Pending[Encoded, Call],
    defBlockers: VectorMap[Call, Encoded],
    constrained: Set[Type],
    congruent: Set[(Call, Call)])

  private[unrolling] object functionsManager extends Manager {
    private[FunctionTemplates] val state = new Snapshots(FunctionsState(Pending.empty, VectorMap.empty, Set.empty, Set.empty))

    private lazy val evaluator = semantics.getEvaluator(using context.withOpts(evaluators.optEvalQuantifiers(false)))

    val incrementals: Seq[IncrementalState] = Seq(state)

    def unrollGeneration: Option[Int] = state.get.calls.generation

    def satisfactionAssumptions: Seq[Encoded] =
      state.get.calls.keys.toSeq.map(b => functionCaches.negations.getOrElseUpdate(b, mkNot(b))) ++
        (if (functionCaches.rankedCalls) Seq(mkNot(diverges)) else Seq.empty)
    def refutationAssumptions: Seq[Encoded] = Seq.empty

    def promoteBlocker(b: Encoded): Boolean = state.get.calls.promote(b) match {
      case Some(calls) =>
        state.update(_.copy(calls = calls))
        true
      case None =>
        false
    }

    def unroll: Clauses = if (state.get.calls.isEmpty) Seq.empty else {
      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val (thisCallInfos, rest) = state.get.calls.dequeue
      state.update(_.copy(calls = rest))
      val remainingBlockers = MutableSet.empty ++ thisCallInfos.map(_._1)

      // an interruption stops the unrolling between blockers, never within the calls of one
      for ((blocker, gen, calls) <- thisCallInfos if calls.nonEmpty && !interrupted;
           _ = remainingBlockers -= blocker;
           call @ Call(callee, args, tpSubst) <- calls) {
        val newCls = new scala.collection.mutable.ListBuffer[Encoded]

        val defBlocker = state.get.defBlockers.get(call) match {
          case Some(defBlocker) =>
            // we already have defBlocker => f(args) = body
            defBlocker

          case None =>
            // we need to define this defBlocker and link it to definition
            val defBlocker = encodeSymbol(Variable.fresh("d", BooleanType(), true))
            state.update(s => s.copy(defBlockers = s.defBlockers.updated(call, defBlocker)))

            callee match {
              case interpreted: Interpreted =>
                newCls ++= Rule.Unfold(InterpretedTemplate(interpreted), defBlocker, args, Some(callFailure(call))).clauses
              case Defined(tfd) =>
                // Ground calls are evaluated rather than unfolded, and unfolded when evaluation fails. A call is
                // blocked if a ground argument that runs no functions gets stuck (e.g. `nil.tail`).
                val (inlining, skip) = context.timers.solvers.`eval-call`.run {
                  val groundArgs = (args zip tfd.params).map { p =>
                    decodePartial(p._1.encoded, p._2.getType)
                      .map(e => exprOps.postMap {
                        case IsTyped(v: Variable, ft: FunctionType) =>
                          lambdaTemplates.find(_.ids._1 == v).map(_.lambda)
                        case _ => None
                      } (e))
                      .filter(exprOps.variablesOf(_).isEmpty)
                  }

                  val groundCall =
                    if (groundArgs.forall(_.isDefined)) Some(tfd.applied(groundArgs.map(_.get)))
                    else None

                  def runsFunctions(arg: Expr): Boolean = exprOps.exists {
                    case (_: FunctionInvocation) | (_: Application) => true
                    case adt: ADT => adt.getConstructor.sort.definition.hasInvariant
                    case _ => false
                  } (arg)

                  val stuck = groundArgs.flatten.exists { arg =>
                    !runsFunctions(arg) && (evaluator.eval(arg) match {
                      case evaluators.EvaluationResults.RuntimeError(_) => !interruptManager.isInterrupted
                      case _ => false
                    })
                  }

                  val inlining = if (stuck) None
                    else groundCall.filter(e => !callsUninterpreted(tfd) && isPure(e)).map(e => evaluator.eval(e))
                  (inlining, stuck)
                }

                val rule =
                  if (skip) Rule.Unreachable(defBlocker)
                  else inlining.flatMap(_.result) match {
                    case Some(value) =>
                      Rule.Unfold(valueTemplate(tfd, value, defBlocker, args), defBlocker, Seq.empty, Some(callFailure(call)))
                    case None => Rule.Unfold(FunctionTemplate(tfd), defBlocker, args ++ tpSubst, Some(callFailure(call)))
                  }
                newCls ++= rule.clauses
            }

            defBlocker
        }

        // We connect it to the defBlocker: blocker => defBlocker
        if (defBlocker != blocker) {
          registerImplication(blocker, defBlocker)
          newCls ++= enables(blocker, defBlocker)
        }

        reporter.debug("Unrolling behind "+call+" ("+newCls.size+")")
        for (cl <- newCls) {
          reporter.debug("  . "+cl)
        }

        newClauses ++= newCls
      }

      // the blockers that an interruption left out are unfolded later
      for ((b, gen, calls) <- thisCallInfos if remainingBlockers(b)) {
        state.update(s => s.copy(calls = s.calls.register(b, gen, calls)))
      }

      reporter.debug(s"   - ${newClauses.size} new clauses")

      newClauses.toSeq
    }
  }
}
