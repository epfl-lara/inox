/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

trait FunctionTemplates { self: Templates =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  import functionsManager._
  import lambdasManager._

  private lazy val assumeChecked = options.findOptionOrDefault(optAssumeChecked)

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
    private val cache: MutableMap[TypedFunDef, FunctionTemplate] = MutableMap.empty

    def apply(tfd: TypedFunDef): FunctionTemplate = cache.getOrElse(tfd, {
      val body: Expr = timers.solvers.simplify.run { simplifyFormula(tfd.fullBody) }

      val tpVars = tfd.tps.flatMap(variableSeq).distinct
      val fdArgs: Seq[Variable] = tfd.params.map(_.toVariable)
      val call: Expr = tfd.applied(fdArgs)

      val start = Variable.fresh("start", BooleanType(), true)
      val pathVar = start -> encodeSymbol(start)
      val arguments = (fdArgs ++ tpVars).map(v => v -> encodeSymbol(v))
      val substMap = arguments.toMap + pathVar

      val tmplClauses: TemplateClauses = {
        val (p, tmplClauses) = mkExprClauses(start, body, substMap)
        val clauses = tmplClauses + (start -> Equals(call, p))

        // Register the function's return as a contract typing to enable
        // induction with refinement types
        if (ContractUnrolling `unroll` tfd.returnType) {
          // The return type only holds for arguments that lie in the parameter types, so
          // it is assumed only once the arguments' membership in these types is shown.
          // Under `optAssumeChecked`, the front-end has checked the arguments of every call, so
          // the return type is assumed directly.
          val (domains, domClauses) = if (assumeChecked) (Seq.empty[Expr], emptyClauses) else
            tfd.params.foldLeft((Seq.empty[Expr], emptyClauses)) { case ((domains, domClauses), vd) =>
              mkTypeClauses(start, vd.tpe, vd.toVariable, substMap, inDomain = true)(using MembershipGenerator) match {
                case (BooleanLiteral(true), _) => (domains, domClauses)
                case (p, pClauses) => (domains :+ p, domClauses +++ pClauses)
              }
            }

          val (conds, exprs, tree, guarded, eqs, tps, equals, lambdas, quants) = clauses +++ domClauses
          val closures = typeOps.variablesOf(tfd.returnType).toSeq.sortBy(_.id).map(v => Left(substMap(v)))
          val call = mkCall(tfd, arguments.map(_._2))
          if (domains.isEmpty) {
            val typing = Typing(tfd.returnType, call, Constraint(trueT, closures, false))
            (conds, exprs, tree, guarded, eqs, tps `merge` Map(pathVar._2 -> Set(typing)), equals, lambdas, quants)
          } else {
            val result = Variable.fresh("result", BooleanType(), true)
            val resultT = encodeSymbol(result)
            val typing = Typing(tfd.returnType, call, Constraint(resultT, closures, false))
            (conds, exprs + (result -> resultT), tree, guarded `merge` (start -> Implies(andJoin(domains), result)),
              eqs, tps `merge` Map(pathVar._2 -> Set(typing)), equals, lambdas, quants)
          }
        } else {
          clauses
        }
      }

      val (contents, str) = Template.contents(
        pathVar, arguments, tmplClauses, optCall = Some(Defined(tfd)))

      val funString : () => String = () => {
        "Template for def " + tfd.signature +
        "(" + tfd.params.map(a => a.id.toString + " : " + a.getType).mkString(", ") + ") : " +
        tfd.getType + " is :\n" + str()
      }

      val res = new FunctionTemplate(contents, funString)
      cache(tfd) = res
      res
    })
  }

  /** The templates of the interpretations of uninterpreted functions, whose calls are the
    * applications of their free functions (see [[TemplateGenerator.interpretedFunctions]]). */
  object InterpretedTemplate {
    private val cache: MutableMap[Interpreted, FunctionTemplate] = MutableMap.empty

    def apply(callee: Interpreted): FunctionTemplate = cache.getOrElse(callee, {
      val Lambda(params, body) = interpretation(callee.id, callee.tps).get: @unchecked
      val args = params.map(_.freshen.toVariable)
      val interpreted = exprOps.replaceFromSymbols((params zip args).toMap, body)

      val start = Variable.fresh("start", BooleanType(), true)
      val pathVar = start -> encodeSymbol(start)
      val arguments = args.map(v => v -> encodeSymbol(v))
      val substMap = arguments.toMap + pathVar

      val (p, clauses) = mkExprClauses(start, interpreted, substMap)
      val tmplClauses = clauses + (start -> Equals(Application(callee.function, args), p))

      val (contents, str) = Template.contents(pathVar, arguments, tmplClauses, optCall = Some(callee))
      val res = new FunctionTemplate(contents, () => "Template for the interpretation of " + callee.signature + " is :\n" + str())
      cache(callee) = res
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
    val gen = nextGeneration(currentGeneration)
    val notBlocker = mkNot(blocker)

    callInfos.get(blocker) match {
      case Some((exGen, origGen, _, exFis)) =>
        // PS: when recycling `b`s, this assertion becomes dangerous.
        // It's better to simply take the max of the generations.
        // assert(exGen == gen, "Mixing the same id "+id+" with various generations "+ exGen+" and "+gen)

        val minGen = gen min exGen

        callInfos += blocker -> (minGen, origGen, notBlocker, exFis + fi)
      case None =>
        callInfos += blocker -> (gen, gen, notBlocker, Set(fi))
    }

    Seq.empty
  }

  def getCalls: Seq[(Encoded, Call)] = defBlockers.toList.map(p => p._2 -> p._1)

  /** Whether calls of `tfd` can reach an uninterpreted function, in which case ground calls of
    * `tfd` can't be evaluated. */
  private val uninterpretedCache: MutableMap[Identifier, Boolean] = MutableMap.empty
  private def callsUninterpreted(tfd: TypedFunDef): Boolean = uninterpretedCache.getOrElseUpdate(tfd.id,
    (transitiveCallees(tfd.fd) + tfd.fd).exists { fd =>
      exprOps.exists { case _: UninterpretedCall => true case _ => false } (fd.fullBody)
    })

  /** Clauses stating that the calls `call1` and `call2` of the same function on equal arguments
    * have equal results, when some of its parameters or its result need equality unrolling.
    *
    * The results of calls are determined by the function body (whose uninterpreted calls are
    * functions of their arguments), so these clauses are only shortcuts and their equalities need
    * not be unrolled.
    */
  private def purityClauses(call1: Call, blocker1: Encoded, call2: Call, blocker2: Encoded): Clauses = call1.callee match {
    // The calls of an interpreted function are applications of the same free function
    case _: Interpreted => Seq.empty
    case Defined(tfd) => if (tfd.params.exists(vd => unrollEquality(vd.getType)) || unrollEquality(tfd.getType)) {
      val clauses = new scala.collection.mutable.ListBuffer[Encoded]
      val equalities = (tfd.params.map(_.getType) zip (call1.args zip call2.args)).map { case (tpe, (e1, e2)) =>
        val (equality, eqClauses) = mkEqualities(blocker1, tpe, e1.encoded, e2.encoded, register = false)
        clauses ++= eqClauses
        equality
      }

      val (entail, entailClauses) = mkEqualities(blocker1, tfd.getType,
        mkCall(tfd, call1.args.map(_.encoded)),
        mkCall(tfd, call2.args.map(_.encoded)), register = false)
      clauses ++= entailClauses

      clauses += mkImplies(mkAnd(blocker1 +: blocker2 +: equalities*), entail)
      clauses.toSeq
    } else {
      Seq.empty
    }
  }

  /** The purity clauses between the calls unrolled so far, which [[equalitiesInstantiated]] delays.
    *
    * Until a first equality is instantiated, the equality symbols of distinct terms are left
    * unconstrained, so the purity clauses can't constrain the results of calls. Each pair of calls of a function on values with a custom equality (e.g. bags
    * on cvc5) gets its own clauses, so delaying them keeps formulas that never compare such values
    * from growing quadratically with the number of calls.
    */
  private[unrolling] def delayedPurityClauses: Clauses = {
    val calls = defBlockers.toSeq.groupBy(_._1.callee)
    for {
      (_, tfdCalls) <- calls.toSeq
      ((call1, blocker1), i) <- tfdCalls.zipWithIndex
      (call2, blocker2) <- tfdCalls.drop(i + 1)
      clause <- purityClauses(call1, blocker1, call2, blocker2)
    } yield clause
  }

  private val callCache: MutableMap[TypedFunDef, (Seq[Encoded], Encoded)] = MutableMap.empty
  private[unrolling] def mkCall(tfd: TypedFunDef, args: Seq[Encoded]): Encoded = {
    val (asT, call) = callCache.getOrElse(tfd, {
      val as = tfd.params.map(vd => Variable.fresh("x", vd.getType, true))
      val asT = as.map(encodeSymbol)
      val res = (asT, mkEncoder((as zip asT).toMap)(tfd.applied(as)))
      callCache(tfd) = res
      res
    })

    mkSubstituter((asT zip args).toMap)(call)
  }

  private[unrolling] object functionsManager extends Manager {
    // Function instantiations have their own defblocker
    private[FunctionTemplates] val defBlockers = new IncrementalMap[Call, Encoded]()

    // Keep which function invocation is guarded by which guard,
    // also specify the generation of the blocker.
    private[FunctionTemplates] val callInfos   = new IncrementalMap[Encoded, (Int, Int, Encoded, Set[Call])]()

    private lazy val evaluator = semantics.getEvaluator(using context.withOpts(evaluators.optEvalQuantifiers(false)))

    val incrementals: Seq[IncrementalState] = Seq(callInfos, defBlockers)

    def unrollGeneration: Option[Int] =
      if (callInfos.isEmpty) None
      else Some(callInfos.values.map(_._1).min)

    def satisfactionAssumptions: Seq[Encoded] = callInfos.map(_._2._3).toSeq
    def refutationAssumptions: Seq[Encoded] = Seq.empty

    def promoteBlocker(b: Encoded): Boolean = {
      if (callInfos `contains` b) {
        val (_, origGen, notB, fis) = callInfos(b)
        callInfos += b -> (currentGeneration, origGen, notB, fis)
        true
      } else {
        false
      }
    }

    def unroll: Clauses = if (callInfos.isEmpty) Seq.empty else {
      val blockers = callInfos.filter(_._2._1 <= currentGeneration).toSeq.map(_._1)

      val newClauses = new scala.collection.mutable.ListBuffer[Encoded]

      val thisCallInfos = blockers.flatMap(id => callInfos.get(id).map(id -> _))
      callInfos --= blockers

      val remainingBlockers = MutableSet.empty ++ blockers

      for ((blocker, (gen, _, _, calls)) <- thisCallInfos if calls.nonEmpty && !abort && !pause;
           _ = remainingBlockers -= blocker;
           call @ Call(callee, args, tpSubst) <- calls if !abort) {
        val newCls = new scala.collection.mutable.ListBuffer[Encoded]

        val defBlocker = defBlockers.get(call) match {
          case Some(defBlocker) =>
            // we already have defBlocker => f(args) = body
            defBlocker

          case None =>
            // we need to define this defBlocker and link it to definition
            val defBlocker = encodeSymbol(Variable.fresh("d", BooleanType(), true))
            defBlockers += call -> defBlocker

            // we generate helper equality clauses that stem from purity (see [[purityClauses]])
            if (equalitiesInstantiated) {
              for ((pcall, pblocker) <- defBlockers if pcall.callee == callee && pcall != call) {
                newClauses ++= purityClauses(pcall, pblocker, call, defBlocker)
              }
            }

            callee match {
              case interpreted: Interpreted =>
                newCls ++= InterpretedTemplate(interpreted).instantiate(defBlocker, args)
              case Defined(tfd) =>
                val (inlining, skip) = context.timers.solvers.`eval-call`.run {
                  val groundArgs = (args zip tfd.params).map { p =>
                    decodePartial(p._1.encoded, p._2.getType)
                      .map(e => exprOps.postMap {
                        case IsTyped(v: Variable, ft: FunctionType) =>
                          byID.values.find(_.ids._1 == v).map(_.lambda)
                        case _ => None
                      } (e))
                      .filter(exprOps.variablesOf(_).isEmpty)
                  }

                  val groundCall =
                    if (groundArgs.forall(_.isDefined)) Some(tfd.applied(groundArgs.map(_.get)))
                    else None

                  val inlining = groundCall.filter(e => !callsUninterpreted(tfd) && isPure(e)).map(e => evaluator.eval(e))
                  val skip = (groundArgs.flatten.map(evaluator.eval) ++ inlining).exists {
                    case evaluators.EvaluationResults.EvaluatorError(_) => true
                    case _ => false
                  }
                  (inlining, skip)
                }

                if (skip) {
                  newCls += mkNot(defBlocker)
                } else {
                  newCls ++= inlining.flatMap(_.result).map { body =>
                    val start = Variable.fresh("cs", BooleanType())
                    val (p, cls) = mkExprClauses(start, body, Map(start -> defBlocker))
                    val tmplClauses = cls + (start -> Equals(tfd.applied, p))

                    val encoding: (Clauses, Calls, Apps, Matchers, Reads, Pointers, () => String) = Template.encode(
                      start -> defBlocker,
                      tfd.params.map(_.toVariable) zip args.map(_.encoded),
                      tmplClauses,
                      optCall = Some(Defined(tfd))
                    )

                    val (clauses, calls, apps, matchers, reads, pointers, _) = encoding
                    val (condVars, exprVars, condTree, types, equalities, lambdas, quants) = tmplClauses.proj
                    val (substClauses, substMap) = Template.substitution(
                      condVars, exprVars, condTree, types, lambdas, quants, pointers, Map.empty, defBlocker)
                    val templateClauses = Template.instantiate(clauses, calls, apps, matchers, reads, equalities, substMap)
                    substClauses ++ templateClauses
                  } getOrElse {
                    FunctionTemplate(tfd).instantiate(defBlocker, args ++ tpSubst)
                  }
                }
            }

            defBlocker
        }

        // We connect it to the defBlocker: blocker => defBlocker
        if (defBlocker != blocker) {
          registerImplication(blocker, defBlocker)
          newCls += mkImplies(blocker, defBlocker)
        }

        reporter.debug("Unrolling behind "+call+" ("+newCls.size+")")
        for (cl <- newCls) {
          reporter.debug("  . "+cl)
        }

        newClauses ++= newCls
      }

      for ((b, (gen, origGen, notB, calls)) <- thisCallInfos if remainingBlockers(b)) callInfos.get(b) match {
        case Some((newGen, _, _, newCalls)) => callInfos += b -> (gen min newGen, origGen, notB, calls ++ newCalls)
        case None => callInfos += b -> (gen, origGen, notB, calls)
      }

      reporter.debug(s"   - ${newClauses.size} new clauses")

      newClauses.toSeq
    }
  }
}
