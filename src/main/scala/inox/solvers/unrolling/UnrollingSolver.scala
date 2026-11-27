/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import theories._
import evaluators._
import combinators._

import scala.collection.immutable.{ListMap, ListSet, VectorMap}
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, ListBuffer}

object optUnrollBound       extends IntOptionDef("unroll-bound", default = -1, "<Int> | -1 (unbounded)")
object optUnrollFactor      extends IntOptionDef("unroll-factor", default = 1, "<PosInt>")
object optFeelingLucky      extends FlagOptionDef("feeling-lucky", false)
object optUnrollAssumptions extends FlagOptionDef("unroll-assumptions", false)
/** How long, in milliseconds, the validation of a lucky model may take (see [[optFeelingLucky]]). */
object optLuckyTimeout      extends IntOptionDef("lucky-timeout", default = 5000, "<PosInt> (milliseconds)")

object optModelFinding      extends IntOptionDef("model-finding", 0, "<PosInt> | 0 (off)") {
  override val parser: OptionParsers.OptionParser[Int] = (s => s match {
    case "" => Some(1)
    case _ => OptionParsers.intParser(s)
  })
}

abstract class AbstractUnrollingSolver private
  (override val program: Program,
   override val context: Context)
  // Alias for `program`, as there are some places where `program` is shadowed.
  (val prog: program.type)
  (val enc: transformers.ProgramTransformer {val sourceProgram: program.type})
  (val programEncoder: transformers.ProgramTransformer {
    val sourceProgram: program.type
    val targetProgram: Program { val trees: enc.targetProgram.trees.type }
  })
  (using val semantics: program.Semantics,
   val targetSemantics: programEncoder.targetProgram.Semantics)
  extends Solver { self =>

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}
  import SolverResponses._

  protected type Encoded

  private def this(prog: Program,
                   context: Context,
                   enc: transformers.ProgramTransformer {val sourceProgram: prog.type},
                   programEncoder: transformers.ProgramTransformer {
                     val sourceProgram: prog.type
                     val targetProgram: Program {val trees: enc.targetProgram.trees.type}
                   })
                  (using semantics: prog.Semantics,
                   semanticsProvider: SemanticsProvider {val trees: enc.targetProgram.trees.type}) =
    this(prog, context)(prog)(enc)(programEncoder)(using semantics, programEncoder.targetProgram.getSemantics(using semanticsProvider))

  def this(prog: Program,
           context: Context,
           enc: transformers.ProgramTransformer {val sourceProgram: prog.type})
          // Given the encoder `enc`, produce a theory encoder of its target program
          (theoriesCtor: enc.type => transformers.ProgramTransformer {
            val sourceProgram: enc.targetProgram.type
            val targetProgram: Program {val trees: enc.targetProgram.trees.type}
          })
          (using semantics: prog.Semantics,
           semanticsProvider: SemanticsProvider {val trees: enc.targetProgram.trees.type}) =
    this(prog, context, enc, enc `andThen` theoriesCtor(enc))

  protected final val s: programEncoder.sourceProgram.trees.type = programEncoder.sourceProgram.trees
  protected final val t: programEncoder.targetProgram.trees.type = programEncoder.targetProgram.trees
  protected final val targetProgram: programEncoder.targetProgram.type = programEncoder.targetProgram

  protected val templates: Templates {
    val program: targetProgram.type
    type Encoded = self.Encoded
  }

  protected val underlying: AbstractSolver {
    val program: targetProgram.type
    type Trees = Encoded
  }

  /** Whether the solver produces proofs (see [[certificates.optProduceProofs]]): a check with
    * proofs (see [[SolverResponses.Proof]]) that is unsat then answers with the certificate of
    * what the solver checked, when the underlying solver proves its refutation. */
  protected final lazy val producesProofs: Boolean = options.findOptionOrDefault(certificates.optProduceProofs)

  /** A rule that the solver applied, with its kind, its arguments and the clauses that it built,
    * which are the instance under `subst` of the clauses of `template` when it instantiates one. */
  private case class Applied(kind: String, arguments: Seq[(String, Seq[Encoded])],
                             template: Option[(templates.TemplateContents, Map[Encoded, Encoded])], clauses: Seq[Encoded])

  // With proofs, the clauses asserted to the underlying solver in its scopes, and the rules that
  // gave them, in the solver's scopes, which certificates are made of
  private val asserted = new IncrementalSeq[Encoded]
  private val rules = new IncrementalSeq[Applied]

  /** Logs a rule application with proofs (see [[RuleChecker.logged]]). */
  protected final def logRule(kind: String, arguments: Seq[(String, Seq[Encoded])],
                              template: Option[(templates.TemplateContents, Map[Encoded, Encoded])], clauses: Seq[Encoded]): Unit =
    rules += Applied(kind, arguments, template, clauses)

  protected final def assertUnderlying(clause: Encoded): Unit = {
    if (producesProofs) asserted += clause
    underlying.assertCnstr(clause)
  }

  protected final def pushUnderlying(): Unit = {
    asserted.push()
    underlying.push()
  }

  protected final def popUnderlying(): Unit = {
    asserted.pop()
    underlying.pop()
  }

  protected final def resetUnderlying(): Unit = {
    asserted.clear()
    rules.clear()
    underlying.reset()
  }

  /** The printer of the solver's terms and sources in the session of the underlying solver, when
    * its session prints them (see [[certificates.Certificates.CertificatePrinter]]). */
  protected def certificatePrinter: Option[certificates.Certificates.Printer[Encoded]] = None

  /** The input of the solver for its certificates, which `printer` prints the sources of: the
    * constraints that were asserted, before the encoders of the program, and what they make of
    * them (see [[certificates.Certificates.Encoding]]). None when the input can't be printed. */
  protected def certificateInput(printer: certificates.Certificates.Printer[Encoded]):
      Option[certificates.Certificates.Encoding[Encoded]] = None

  /** The constraints that were asserted, in the scopes of the solver. */
  protected final def assertedConstraints: Seq[Expr] = constraints.toSeq

  /** The certificate of a check of a query under `queryAssumptions`, which answers unsat from a
    * check of the underlying solver under `assumptions` that it proved unsat with `proof`: the
    * clauses that the underlying solver has, the assumptions, and the rules that gave them. */
  private def certify(assumptions: Seq[Encoded], proof: Either[String, certificates.Proof],
                      queryAssumptions: Set[Encoded]): Either[String, certificates.Proof] = proof match {
    case Left(why) => Left(why)
    case Right(proof: certificates.ScriptProof) =>
      val clauses = asserted.toSeq
      import certificates.Certificates.{Refutation, TemplateClauses, AppliedRule, Assumed}
      import certificates.{Argument, Instance, Value}
      val inScope = clauses.toSet
      // a rule may give clauses that this check doesn't have, when the solver didn't assert them
      val applied = rules.toSeq.map(r => r.copy(clauses = r.clauses.filter(inScope))).filter(_.clauses.nonEmpty)
      // each template once, in the order of the rules
      val index = new java.util.IdentityHashMap[templates.TemplateContents, Int]
      for (r <- applied; (contents, _) <- r.template if !index.containsKey(contents)) index.put(contents, index.size)
      import scala.jdk.CollectionConverters._
      val contents = index.asScala.toSeq.sortBy(_._2).map(_._1)
      val ruleSeq = applied.map { r =>
        // the values of the start blocker and arguments, which are themselves when not given, then
        // of the fresh symbols
        AppliedRule(r.kind, r.arguments.map(Argument(_, _)), r.template.map { case (contents, subst) =>
          val params = contents.pathVar._2 +: contents.args
          Instance(index.get(contents): Int,
            (params.map(p => p -> subst.getOrElse(p, p)) ++ subst.toSeq.filterNot(kv => params.contains(kv._1))).map(Value(_, _)))
        }, r.clauses)
      }
      // a refutation only assumes the query's assumptions and what refutations may assume
      val assumed = assumptions.map(a => Assumed(a, complete = !queryAssumptions(a) && templates.assumedComplete(a)))
      assumptions.find(a => !queryAssumptions(a) && !templates.assumedComplete(a)) match {
        case Some(a) => Left("the check that refuted the query assumes " + templates.asString(a) + ", which refutations don't assume")
        case None if contents.exists(_.source.isEmpty) => Left("a template of the refutation has no source")
        case None => certificatePrinter match {
          case Some(printer) =>
            val templateSeq = contents.map(c => TemplateClauses(c.pathVar._2 +: c.args, c.clauses, c.source.get))
            printer.define(templates.definition)
            printer.defineSteps(templates.definitionSteps)
            certificates.Certificates.certificate(proof,
              Refutation(clauses, assumed, templateSeq, ruleSeq, certificateInput(printer)), printer,
              functionEquality.toString.toLowerCase)
          case None => Left("the underlying solver's session doesn't print the solver's terms")
        }
      }
    case Right(proof) =>
      Left(s"the underlying solver's proof is not one of a script ($proof)")
  }

  protected final def encode(vd: ValDef): t.ValDef = programEncoder.encode(vd)
  protected final def decode(vd: t.ValDef): ValDef = programEncoder.decode(vd)

  protected final def encode(v: Variable): t.Variable = programEncoder.encode(v)
  protected final def decode(v: t.Variable): Variable = programEncoder.decode(v)

  protected final def encode(e: Expr): t.Expr = programEncoder.encode(e)
  protected final def decode(e: t.Expr): Expr = programEncoder.decode(e)

  protected final def encode(tpe: Type): t.Type = programEncoder.encode(tpe)
  protected final def decode(tpe: t.Type): Type = programEncoder.decode(tpe)

  lazy val checkModels = options.findOptionOrDefault(optCheckModels)
  lazy val ignoreModels = options.findOptionOrDefault(optIgnoreModels)
  lazy val silentErrors = options.findOptionOrDefault(optSilentErrors)
  lazy val unrollBound = options.findOptionOrDefault(optUnrollBound)
  lazy val unrollFactor = options.findOptionOrDefault(optUnrollFactor)
  lazy val feelingLucky = options.findOptionOrDefault(optFeelingLucky)
  lazy val luckyTimeout = options.findOptionOrDefault(optLuckyTimeout)
  lazy val unrollAssumptions = options.findOptionOrDefault(optUnrollAssumptions)
  lazy val modelFinding = options.findOptionOrDefault(optModelFinding) > 0

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    checkAssumptions(config)(Set.empty)

  private var unrollBoundHit: Boolean = false
  override def unrollBoundReached: Boolean = unrollBoundHit

  protected val freeVars  = new IncrementalMap[Variable, Encoded]()
  private val constraints = new IncrementalSeq[Expr]()

  /** The equality literals of the on-demand distinguishing inputs that the last model extraction
    * needed (see [[LambdaTemplates.onDemandWitnesses]]). */
  private var requestedWitnesses: Map[Encoded, Int] = Map.empty

  /** The on-demand distinguishing inputs of the functions that show up in the last extracted model,
    * which then join the regular unfolding (see [[LambdaTemplates.promoteWitnesses]]). */
  private var exposedWitnesses: Set[Encoded] = Set.empty

  protected var failures: ListBuffer[Throwable] = new ListBuffer
  protected var abort: Boolean = false

  def push(): Unit = {
    rules.push()
    templates.push()
    constraints.push()
    freeVars.push()
  }

  def pop(): Unit = {
    rules.pop()
    templates.pop()
    constraints.pop()
    freeVars.pop()
  }

  def reset() = {
    failures.clear()
    abort = false
    if (evaluatorInterrupts.isInterrupted) evaluatorInterrupts.reset()

    templates.reset()
    constraints.reset()
    freeVars.reset()
    resetUnderlying()
  }

  def interrupt(): Unit = {
    abort = true
    if (!evaluatorInterrupts.isInterrupted) evaluatorInterrupts.interrupt()
  }

  def free(): Unit = context.interruptManager.unregisterForInterrupts(this)

  protected def declareVariable(v: t.Variable): Encoded

  /** Asserts `clause` for good, as a clause that a rule built (see [[RuleChecker]]). */
  private def assertClause(clause: Encoded): Unit = {
    templates.checkAsserted(clause)
    assertUnderlying(clause)
  }

  /** The model that the solver operates under, as when an evaluator solves for the foralls of an
    * expression that it evaluates in this model (see [[SolverFactory.getFromName]]).
    * The uninterpreted functions that the model interprets take their values in the model instead of
    * arbitrary ones. */
  protected def partialModel: program.Model = inox.Model.empty(program)

  /** The interpretation that the partial model gives to the uninterpreted function `id` at `tps`, if
    * it interprets it (see [[TemplateGenerator.interpretation]]). */
  protected final def interpretation(id: Identifier, tps: Seq[t.Type]): Option[t.Lambda] =
    partialModel.interpretations.get(id -> tps.map(decode(_))).collect {
      case l: Lambda => encode(l).asInstanceOf[t.Lambda]
    }

  def declare(vd: ValDef): Unit = context.timers.solvers.declare.run(try {
    context.timers.solvers.declare.sanity.run {
      assert(vd.getType.isTyped)
    }

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

    val freeBindings: Map[Variable, Encoded] = orderedBindings(typeOps.variablesOf(vd.tpe) + vd.toVariable)

    val newClauses = context.timers.solvers.declare.clauses.run {
      templates.unfolding.instantiateVariable(encode(vd.toVariable), freeBindings.map(p => encode(p._1) -> p._2))
    }

    context.timers.solvers.declare.underlying.run {
      for (cl <- newClauses) {
        assertClause(cl)
      }
    }
  } catch {
    case e @ (_: InternalSolverError | _: Unsupported) => failures += e
  })

  lazy val functionEquality = options.findOptionOrDefault(optFunctionEquality)

  /** Rejects `expression` if it compares values that contain functions, either directly or through
    * the functions it calls (see [[optFunctionEquality]]). */
  private def checkNoFunctionComparisons(expression: Expr): Unit = {
    val violations = FunctionEquality.comparisons(program)(expression)
    if (violations.nonEmpty) {
      throw new TypeErrorException(
        "Functions can't be compared under --function-equality=none: " +
          violations.map(_.asString).mkString(", "), violations.head, violations.head.getPos)
    }

    val collections = FunctionEquality.functionKeyedCollections(program)(expression)
    if (collections.nonEmpty) {
      throw new TypeErrorException(
        "Sets and bags of functions and maps with function keys compare functions, which can't be " +
          "compared under --function-equality=none: " +
          collections.map(e => s"${e.asString}: ${e.getType.asString}").mkString(", "),
        collections.head, collections.head.getPos)
    }
  }

  /** The encodings of `vars`, declared in the order of their identifiers, and in that order in the
    * map: a set of variables iterates in the order of their hashes, which depend on how many
    * identifiers were created before, and the order of the declarations and of the clauses about
    * them changes how much work the underlying solver does. */
  private def orderedBindings(vars: Set[Variable]): Map[Variable, Encoded] =
    ListMap.from(vars.toSeq.sortBy(_.id).map {
      v => v -> freeVars.cached(v)(declareVariable(encode(v)))
    })

  def assertCnstr(expression: Expr): Unit = context.timers.solvers.assert.run(try {
    context.timers.solvers.assert.sanity.run {
      symbols.ensureWellFormed // make sure that the current program is well-formed
      typeCheck(expression, BooleanType(), PropType()) // make sure we've asserted a boolean or a proposition
      if (functionEquality == FunctionEquality.None) checkNoFunctionComparisons(expression)
    }

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

    constraints += expression

    val freeBindings: Map[Variable, Encoded] = orderedBindings(exprOps.variablesOf(expression))

    val newClauses = context.timers.solvers.assert.clauses.run {
      templates.unfolding.instantiateExpr(
        encode(expression),
        freeBindings.map(p => encode(p._1) -> p._2)
      )
    }

    context.timers.solvers.assert.underlying.run {
      for (cl <- newClauses) {
        assertClause(cl)
      }
    }
  } catch {
    case e @ (_: InternalSolverError | _: Unsupported) => failures += e
  })

  protected def wrapModel(model: underlying.Model): ModelWrapper

  trait ModelWrapper {
    def modelEval(elem: Encoded, tpe: t.Type): Option[t.Expr]

    def extractConstructor(elem: Encoded, tpe: t.ADTType): Option[Identifier]
    def extractSet(elem: Encoded, tpe: t.SetType): Option[Seq[Encoded]]
    def extractMap(elem: Encoded, tpe: t.MapType): Option[(Seq[(Encoded, Encoded)], Encoded)]
    def extractBag(elem: Encoded, tpe: t.BagType): Option[Seq[(Encoded, Encoded)]]

    /** The value of the uninterpreted function `id` that the extracted values call, if any. */
    def getUninterpreted(id: Identifier): Option[t.Expr]

    def eval(elem: Encoded, tpe: Type): Option[Expr] = modelEval(elem, encode(tpe)).flatMap {
      expr => try {
        Some(decode(expr))
      } catch {
        case u: Unsupported => None
      }
    }

    def getModel(extract: (Encoded, Type) => Expr): program.Model = {
      // Functions that are equal in the model share their extraction, so variables with refined
      // types are extracted first for the shared value to lie in these types.
      val extracted = freeVars.toSeq.sortBy { case (v, _) => v.tpe == v.getType }
        .map { case (v, idT) => v -> extract(idT, v.tpe) }.toMap

      // The default values of function models may refer to the free variables of their types
      val allVs = extracted.map { case (v, e) => v.toVal -> exprOps.replaceFromSymbols(extracted, e) }

      // The free functions that stand for uninterpreted functions give their models, and their
      // applications in values are calls to these functions again
      val uninterpreted = templates.model.uninterpretedFunctions.toSeq.map { case ((id, tps), (f, fT)) =>
        (id, tps.map(decode(_))) -> (decode(f).asInstanceOf[Variable], fT)
      }
      val byFunction = uninterpreted.map { case (key, (f, _)) => f -> key }.toMap
      // Their models are extracted at their full types, so that they lie in their codomains
      val uninterpretedTypes = templates.model.uninterpretedTypes.toSeq.map { case ((id, tps), tpe) =>
        (id, tps.map(decode(_))) -> decode(tpe)
      }.toMap
      val constants = templates.model.uninterpretedConstants.map { case (id, tps) => (id, tps.map(decode(_))) }
      def restore(e: Expr): Expr = exprOps.postMap {
        case Application(f: Variable, args) if byFunction contains f =>
          val (id, tps) = byFunction(f)
          Some(UninterpretedCall(id, tps, args, f.getType))
        case f: Variable if byFunction.get(f).exists(constants) =>
          val (id, tps) = byFunction(f)
          Some(UninterpretedCall(id, tps, Seq.empty, FunctionType(Seq.empty, f.getType)))
        case _ => None
      } (e)
      // The model that the solver operates under gives the functions that it interprets
      val uninterpretedVs = uninterpreted.collect { case (key, (f, fT)) if !partialModel.interpretations.contains(key) =>
        val tpe = uninterpretedTypes.getOrElse(key, f.getType)
        key -> exprOps.replaceFromSymbols(extracted, (tpe, constants(key)) match {
          // The calls of constants are their values
          case (FunctionType(Seq(), to), true) => Lambda(Seq.empty, extract(fT, to))
          case _ => extract(fT, tpe)
        })
      }.toMap
      val vs = allVs.map { case (vd, e) => vd -> restore(e) }

      // The values may contain the calls of closures and extracted functions (see `uniquateClosure`),
      // whose uninterpreted functions the underlying model gives at no type arguments
      def interpretationsOf(e: Expr): Map[(Identifier, Seq[Type]), Expr] = {
        def rec(es: Seq[Expr], acc: Map[(Identifier, Seq[Type]), Expr]): Map[(Identifier, Seq[Type]), Expr] = {
          val cs = es.flatMap(exprOps.collect {
            case UninterpretedCall(id, Seq(), _, _) if !acc.contains(id -> Seq()) =>
              getUninterpreted(id).map(e => (id, Seq.empty[Type]) -> decode(e)).toSet
            case _ => Set.empty[((Identifier, Seq[Type]), Expr)]
          }).toMap
          if (cs.isEmpty) acc else rec(cs.values.toSeq, acc ++ cs)
        }
        rec(Seq(e), Map.empty)
      }

      val modelCs = (vs.values ++ uninterpretedVs.values).toSeq.flatMap(interpretationsOf)

      val modelInterpretations = (modelCs ++ uninterpretedVs).map { case (k, e) => k -> restore(e) }.toMap

      // The lambdas of the program that the model unblocks, with the values that they capture, or
      // only their types when these values can't be extracted
      val active: Seq[Either[FunctionType, Lambda]] = templates.model.lambdaTemplates
        .filter(tmpl => modelEval(tmpl.start, t.BooleanType()) == Some(t.BooleanLiteral(true)))
        .map { tmpl =>
          val lambda = decode(tmpl.structure.body).asInstanceOf[Lambda]
          try {
            val locals = tmpl.structure.locals.map { case (v, ev) => decode(v) -> extract(ev, decode(v).getType) }
            Right(restore(exprOps.replaceFromSymbols(locals.toMap, lambda)).asInstanceOf[Lambda])
          } catch {
            case _: NoSimpleValue | _: Unsupported => Left(lambda.getType.asInstanceOf[FunctionType])
          }
        }

      val (inlinedVs, inlinedCs) = inlineUnambiguousClosures(vs, modelInterpretations, active)
      inox.Model(program)(inlinedVs, inlinedCs)
    }
  }

  /** Inlines the closures of a model (see `uniquateClosure`) whose functions no other function of the
    * model matches, as they need no uninterpreted function to stay distinct. The functions of the
    * model include the `active` lambdas of the program, which are those that evaluating the
    * constraints in the model can reach, or their types when their captured values are unknown.
    * The functions that the remaining closures call stay in the
    * model. */
  private def inlineUnambiguousClosures(
    vs: Map[ValDef, Expr],
    interpretations: Map[(Identifier, Seq[Type]), Expr],
    active: Seq[Either[FunctionType, Lambda]]
  ): (Map[ValDef, Expr], Map[(Identifier, Seq[Type]), Expr]) = {
    object Closure {
      def unapply(e: Expr): Option[(Identifier, Lambda)] = e match {
        case l @ Lambda(params, UninterpretedCall(id, Seq(), args, _))
            if args == params.map(_.toVariable) => interpretations.get(id -> Seq()) match {
          case Some(f: Lambda) if f.getType == l.getType => Some(id -> f)
          case _ => None
        }
        case _ => None
      }
    }

    def normal(l: Lambda): Expr = {
      val (nl, subst) = normalizeStructure(l, ast.SymbolOps.NormalizationLifting.Simple)
      exprOps.replaceFromSymbols(subst.map { case (v, e, _) => v -> e }.toMap, nl)
    }

    val values = vs.values.toSeq ++ interpretations.values
    val closures = values.flatMap(exprOps.collect[(Identifier, Lambda)] {
      case Closure(id, f) => Set(id -> f)
      case _ => Set.empty
    }).toMap
    // The functions that closures call are only counted through their closures
    val otherValues = vs.values.toSeq ++ interpretations.toSeq.map {
      case ((id, Seq()), l: Lambda) if closures.contains(id) => l.body
      case (_, e) => e
    }
    val others = otherValues.flatMap(exprOps.collect[Lambda] {
      case Closure(_, _) => Set.empty
      case l: Lambda => Set(l)
      case _ => Set.empty
    })

    // The functions of a closure are only inlined when no other function of the model has their
    // structure, including the functions of the other closures and the lambdas that the model
    // unblocks. The active lambdas whose captured values are unknown may have any structure.
    val counts = (closures.values.toSeq ++ others ++ active.flatMap(_.toOption))
      .groupBy(l => (l.getType, normal(l))).view.mapValues(_.size).toMap
    val opaque = active.flatMap(_.left.toOption).toSet[Type]
    val inlined = closures.filter { case (_, f) => counts((f.getType, normal(f))) == 1 && !opaque(f.getType) }

    if (inlined.isEmpty) (vs, interpretations) else {
      // The inlined functions may themselves contain closures, which are inlined in turn
      def inlineIn(e: Expr, seen: Set[Identifier]): Expr = exprOps.postMap {
        case Closure(id, _) if inlined.contains(id) && !seen(id) => Some(inlineIn(inlined(id), seen + id))
        case _ => None
      } (e)

      val newVs = vs.map { case (vd, e) => vd -> inlineIn(e, Set.empty) }
      val newCs = interpretations.map { case (k, e) => k -> inlineIn(e, Set.empty) }

      // The functions of inlined closures stay only where the remaining values still call them
      val called = (newVs.values ++ newCs.values).flatMap(exprOps.collect[Identifier] {
        case UninterpretedCall(id, Seq(), _, _) => Set(id)
        case _ => Set.empty
      }).toSet
      (newVs, newCs.filter { case ((id, tps), _) => !inlined.contains(id) || tps.nonEmpty || called(id) })
    }
  }

  /** The interrupt manager of the solver's evaluators, which the solver's interrupts reach: the
    * extraction and the validation of a huge model then stop (see `RecursiveEvaluator.e`).
    */
  protected lazy val evaluatorInterrupts: InterruptManager = new InterruptManager(reporter)

  // Model values are compared as the solver sees them: functions are equal iff they are the same
  // function value, which the encoding makes structural (see [[optFunctionEquality]]).
  protected lazy val modelEvalContext: Context = context.copy(interruptManager = evaluatorInterrupts).withOpts(
    optIgnoreContracts(true), optFunctionEquality(FunctionEquality.Intensional))

  protected lazy val modelEvaluator: DeterministicEvaluator { val program: self.targetProgram.type } =
    targetSemantics.getEvaluator(using modelEvalContext)

  private def emit(silenceErrors: Boolean)(msg: String) =
    if (silenceErrors) reporter.debug(msg) else reporter.warning(msg)

  private def validateModel(model: program.Model, assumptions: Seq[Expr], silenceErrors: Boolean): Boolean = {
    // the values of the model have the types that it gives to the type parameters
    val formulas = (assumptions ++ constraints).map(typeOps.instantiateType(_, model.types))
    val expr = andJoin(formulas)

    // The uninterpreted functions whose models the typing conditions are being expanded through
    val expanding = MutableSet.empty[Identifier]
    def typing(value: Expr, tpe: Type): Expr = {
      def rec(e: Expr, tpe: Type): Expr = (e, tpe) match {
        // The models of functions are conditionals over their arguments, and their default values
        // are chosen in their codomains (see `defaultValue`)
        case (Let(vd, value, body), tpe) => Let(vd, value, rec(body, tpe)).copiedFrom(body)
        case (IfExpr(cond, thenn, elze), tpe) => IfExpr(cond, rec(thenn, tpe), rec(elze, tpe)).copiedFrom(e)
        // The default values of the models of functions are solved for in their refined codomains
        // (see `defaultValue`)
        case (uc: UninterpretedCall, _) if !model.interpretations.contains(uc.id -> uc.tps) &&
          uc.getTpe(stripRefinements = false) != uc.getType => BooleanLiteral(true)
        case (ADT(id, _, args), adt @ ADTType(_, tps)) =>
          // Field types may refer to the other fields of the constructor
          val fields = getConstructor(id, tps).fields
          andJoin((args zip fields).map(p => rec(p._1, p._2.tpe))) match {
            case BooleanLiteral(true) => BooleanLiteral(true)
            case p => (fields zip args).foldRight(p) { case ((vd, e), p) => Let(vd, e, p).copiedFrom(p) }
          }
        case (Tuple(es), TupleType(tps)) =>
          andJoin((es zip tps).map(p => rec(p._1, p._2)))
        case (FiniteSet(elems, _), SetType(base)) =>
          andJoin(elems.map(e => rec(e, base)))
        case (FiniteBag(elems, _), BagType(base)) =>
          andJoin(elems.map(p => and(rec(p._1, base), rec(p._2, IntegerType()))))
        case (FiniteMap(elems, dflt, _, _), MapType(from, to)) =>
          andJoin(elems.map(p => and(rec(p._1, from), rec(p._2, to))) :+ rec(dflt, to))
        // The models of functions may build the collections that they return by updates
        case (SetAdd(set, elem), SetType(base)) =>
          and(rec(set, tpe), rec(elem, base))
        case (BagAdd(bag, elem), BagType(base)) =>
          and(rec(bag, tpe), rec(elem, base))
        case (MapUpdated(map, key, value), MapType(from, to)) =>
          andJoin(Seq(rec(map, tpe), rec(key, from), rec(value, to)))
        case (Lambda(params, body), FunctionType(from, to)) =>
          val nparams = (params zip from).map { case (vd, tpe) => vd.copy(tpe = tpe) }
          forall(nparams, rec(
            exprOps.replaceFromSymbols((params zip nparams.map(_.toVariable)).toMap, body), to))
        // The calls of the functions that the model gives lie in a type when the bodies of their
        // models do, whose default values are chosen in their codomains (see `defaultValue`)
        case (UninterpretedCall(id, tps, args, _), tpe) if !expanding(id) && model.interpretations.contains(id -> tps) =>
          model.interpretations(id -> tps) match {
            case l: Lambda if l.params.size == args.size =>
              expanding += id
              val cond = rec(exprOps.replaceFromSymbols((l.params.map(_.toVariable) zip args).toMap, l.body), tpe)
              expanding -= id
              cond
            case _ => BooleanLiteral(false)
          }
        case (_, RefinementType(vd, pred)) =>
          and(rec(e, vd.tpe), Let(vd, e, pred).copiedFrom(e))
        case (Lambda(params, body), PiType(nparams, to)) =>
          forall(nparams, rec(
            exprOps.replaceFromSymbols((params zip nparams.map(_.toVariable)).toMap, body), to))
        case (Tuple(es), SigmaType(nparams, to)) =>
          andJoin(
            (es.init zip nparams).map(p => rec(p._1, p._2.tpe)) ++ (rec(es.last, to) match {
              case BooleanLiteral(true) => None
              case p => Some((nparams zip es.init).foldRight(p) {
                case ((vd, e), p) => Let(vd, e, p).copiedFrom(p)
              })
            })
          )
        // The closures of models call the functions that the model gives (see `uniquateClosure`)
        case (UninterpretedCall(id, Seq(), args, _), tpe) if !expanding(id) => model.interpretations.get(id -> Seq()) match {
          case Some(l: Lambda) if l.params.size == args.size =>
            expanding += id
            val cond = rec(exprOps.replaceFromSymbols((l.params.map(_.toVariable) zip args).toMap, l.body), tpe)
            expanding -= id
            cond
          case _ => BooleanLiteral(false)
        }
        case _ => BooleanLiteral(true)
      }

      rec(value, tpe)
    }

    // The results of the uninterpreted calls of the constraints lie in their types, where the
    // arguments of these calls are given by the model
    val modelVars = model.vars.keySet.map(_.toVariable)
    val callTypings = formulas.flatMap(exprOps.collect[UninterpretedCall] {
      // The calls that the model doesn't interpret can't be evaluated, so validation fails on them
      case uc: UninterpretedCall if exprOps.variablesOf(uc).subsetOf(modelVars) &&
        model.interpretations.contains(uc.id -> uc.tps) => Set(uc)
      case _ => Set.empty
    }).distinct.map(uc => typing(uc, uc.getTpe(stripRefinements = false)))

    val typingCond = andJoin(model.vars.toSeq.map { case (v, value) => typing(value, v.tpe) } ++ callTypings)

    // we have to check case class constructors in model for ADT invariants
    val newExpr = model.vars.toSeq.foldRight(and(typingCond, expr)) {
      case ((v, value), e) => Let(v, value, e)
    }

    val evaluator = semantics.getEvaluator(using context.copy(interruptManager = evaluatorInterrupts).withOpts(
      optSilentErrors(silenceErrors),
      optCheckModels(checkModels || feelingLucky)
    ))

    val evalModel = inox.Model(program)(Map.empty, partialModel.interpretations ++ model.interpretations, model.types)
    evaluator.eval(newExpr, evalModel) match {
      case EvaluationResults.Successful(BooleanLiteral(true)) =>
        reporter.debug("- Model validated.")
        true

      case EvaluationResults.Successful(_) =>
        reporter.debug("- Invalid model.")
        false

      case EvaluationResults.RuntimeError(msg) =>
        emit(silenceErrors)("- Model leads to runtime error: " + msg)
        false

      case EvaluationResults.EvaluatorError(msg) =>
        emit(silenceErrors)("- Model leads to evaluation error: " + msg)
        false
    }
  }

  /** Runs the validation of a lucky model, which fails once [[luckyTimeout]] has elapsed.
    *
    * A lucky model is only a shortcut to a counterexample that the search would find later, but
    * its validation evaluates the foralls of the program with nested solvers (see
    * [[evaluators.SolvingEvaluator]]), which can take much longer than the search itself.
    */
  private def withinLuckyTimeout(validation: => Boolean): Boolean = {
    var expired = false
    val expiry = new Interruptible {
      def interrupt(): Unit = evaluatorInterrupts.synchronized {
        if (!evaluatorInterrupts.isInterrupted) {
          expired = true
          evaluatorInterrupts.interrupt()
        }
      }
    }

    try new TimeoutFor(expiry).interruptAfter(luckyTimeout.toLong)(validation) finally {
      evaluatorInterrupts.synchronized {
        // The solver may have been interrupted in the meantime, in which case its evaluators stay so
        if (expired && !abort && evaluatorInterrupts.isInterrupted) {
          reporter.debug("- Lucky model validation timed out.")
          evaluatorInterrupts.reset()
        }
      }
    }
  }

  private def extractSimpleModel(model: underlying.Model): program.Model = {
    val wrapped = wrapModel(model)
    wrapped.getModel((e, tpe) => wrapped.eval(e, tpe.getType).getOrElse(simplestValue(tpe.getType)))
  }

  private case class Canceled() extends Exception("Cancelation occurred while extracting model")

  private def extractTotalModel(model: underlying.Model): program.Model = {
    extension[T] (opt: Option[T]) {
      private def getOrThrow: T = opt match {
        case Some(t) => t
        case None =>
          if (abort) {
            // We got a None but were interrupted. Maybe this None is due to the cancellation,
            // so we throw a Canceled that will be caught by checkAssumptions
            throw Canceled()
          } else {
            // We got a None, but not due to interruption. This is likely a bug, this exception will not be caught.
            throw java.util.NoSuchElementException("None.get")
          }
      }
    }

    val wrapped = wrapModel(model)

    import targetProgram._
    import targetProgram.trees._
    import targetProgram.symbols.{given, _}

    // maintain extracted functions to make sure equality is well-defined
    var lambdaExtractions: Seq[(Encoded, Lambda)] = Seq.empty
    // the uninterpreted constants that stand for functions that are being extracted
    var functionExtractions: Seq[(Encoded, UninterpretedCall)] = Seq.empty
    // the uninterpreted functions that the closures which keep extracted functions distinct call
    var closureExtractions: Seq[(Identifier, Lambda)] = Seq.empty
    // the functions that are being extracted as the lambdas they are equal to, and those of them
    // whose lambda captures them, and which are then extracted from their applications instead
    var lambdasInProgress: Seq[Encoded] = Seq.empty
    var capturedByTheirLambda: Seq[Encoded] = Seq.empty

    // evaluating in the model can be costly, and extraction compares the same functions repeatedly
    val modelEqualities = MutableMap.empty[(Encoded, Encoded), Boolean]
    def modelEq(e1: Encoded, e2: Encoded): Boolean = e1 == e2 || modelEqualities.getOrElseUpdate(e1 -> e2,
      wrapped.modelEval(templates.mkEquals(e1, e2), BooleanType()) == Some(BooleanLiteral(true)))

    lazy val onDemandWitnesses = templates.witnesses.onDemand.groupMap(_._1)(_._2)
    // the functions that show up in the model, by type
    val extractedFunctions = MutableMap.empty[FunctionType, Set[Encoded]]

    def extractValue(v: Encoded, tpe: Type, seen: Map[FunctionType, Set[Encoded]]): Expr = {

      // Functions are returned with their full (possibly dependent) types, as the default values
      // of their models must lie in their codomains (@see [[extractFunction]]).
      def functionsOf(v: Encoded, tpe: Type): (Seq[(Encoded, Type)], Seq[Expr] => Expr) = {
        def reconstruct(subs: Seq[(Seq[(Encoded, Type)], Seq[Expr] => Expr)],
                        recons: Seq[Expr] => Expr): (Seq[(Encoded, Type)], Seq[Expr] => Expr) =
          (subs.flatMap(_._1), (exprs: Seq[Expr]) => {
            var curr = exprs
            recons(subs.map { case (es, recons) =>
              val (used, remaining) = curr.splitAt(es.size)
              curr = remaining
              recons(used)
            })
          })

        def rec(v: Encoded, tpe: Type): (Seq[(Encoded, Type)], Seq[Expr] => Expr) = tpe match {
          case (_: FunctionType | _: PiType) =>
            (Seq(v -> tpe), es => es.head)

          case RefinementType(vd, _) =>
            rec(v, vd.tpe)

          case SigmaType(params, to) =>
            // The type of the last element depends on the previous ones, which are substituted in its value
            val (functions, recons) = rec(v, TupleType(params.map(_.tpe) :+ to))
            (functions, es => recons(es) match {
              case Tuple(es) => Tuple(es.init :+ exprOps.replaceFromSymbols((params zip es.init).toMap, es.last))
              case e => e
            })

          case TupleType(tps) =>
            val id = Variable.fresh("tuple", tpe)
            val encoder = templates.mkEncoder(Map(id -> v))
            reconstruct(tps.zipWithIndex.map {
              case (tpe, index) => rec(encoder(TupleSelect(id, index + 1)), tpe)
            }, Tuple.apply)

          case tpe @ ADTType(sid, tps) =>
            val cons = wrapped.extractConstructor(v, tpe).getOrThrow
            val id = Variable.fresh("adt", tpe)
            val encoder = templates.mkEncoder(Map(id -> v))
            reconstruct(getConstructor(cons, tps).fields.map {
              vd => rec(encoder(ADTSelector(id, vd.id)), vd.tpe)
            }, ADT(cons, tps, _))

          case st @ SetType(base) =>
            val vs = wrapped.extractSet(v, st).getOrThrow
            reconstruct(vs.map(rec(_, base)), FiniteSet(_, base))

          case mt @ MapType(from, to) =>
            val (vs, dflt) = wrapped.extractMap(v, mt).getOrThrow
            reconstruct(vs.flatMap(p => Seq(rec(p._1, from), rec(p._2, to))) :+ rec(dflt, to), {
              case es :+ default => FiniteMap(es.grouped(2).map(s => s(0) -> s(1)).toSeq, default, from, to)
            })

          case bt @ BagType(base) =>
            val vs = wrapped.extractBag(v, bt).getOrThrow
            reconstruct(vs.map(p => rec(p._1, base)), es => FiniteBag((es zip vs).map {
              case (k, (_, v)) => k -> wrapped.modelEval(v, IntegerType()).getOrThrow
            }, base))

          case _ => (Seq.empty, (es: Seq[Expr]) => wrapped.modelEval(v, tpe).getOrThrow)
        }

        rec(v, tpe)
      }

      val ev = wrapped.modelEval(v, tpe.getType).filterNot(_.isInstanceOf[Variable])
      if (ev.isDefined) {
        val (functions, recons) = functionsOf(v, tpe)
        recons(functions.map { case (f, tpe) =>
          extractFunction(f, tpe, seen)
        })
      } else {
        unknownValue(tpe)
      }
    }

    /* A value of `tpe` for an element that the model doesn't give, such as a function that is never
     * applied. The simplest value of a function type may not lie in a refined codomain, so functions
     * get the default value of their models instead (see [[defaultValue]]). */
    def unknownValue(tpe: Type): Expr = tpe match {
      // the base type can bind variables whose types hold functions, which only its erasure shows
      case RefinementType(vd, _) if !hasFunctions(vd.getType) =>
        encode(program.symbols.simplestValue(decode(tpe.getType)))
      case RefinementType(vd, _) => unknownValue(vd.tpe)
      case _: FunctionType | _: PiType =>
        val (params, paramTypes, resultType) = signature(tpe)
        Lambda(params, defaultValue(params, paramTypes, resultType)
          .getOrElse(unknownValue(resultType)))
      case _ => encode(program.symbols.simplestValue(decode(tpe.getType)))
    }

    /** Fresh parameters for the function type `fullType`, with its parameter and result types in
      * terms of these parameters. */
    def signature(fullType: Type): (Seq[ValDef], Seq[Type], Type) = {
      val tpe = fullType.getType.asInstanceOf[FunctionType]
      val params: Seq[ValDef] = tpe.from.map(tpe => ValDef.fresh("x", tpe, true))
      fullType match {
        case PiType(ps, to) =>
          val subst: Map[ValDef, Expr] = (ps zip params.map(_.toVariable)).toMap
          (params, ps.map(vd => typeOps.replaceFromSymbols(subst, vd.tpe)), typeOps.replaceFromSymbols(subst, to))
        case FunctionType(from, to) => (params, from, to)
        case _ => (params, tpe.from, tpe.to)
      }
    }

    /** Whether values of type `tpe` can contain functions. */
    def hasFunctions(tpe: Type, seen: Set[Identifier] = Set.empty): Boolean = tpe match {
      case _: FunctionType | _: PiType => true
      case adt: ADTType =>
        !seen(adt.id) && adt.getSort.constructors.exists(_.fields.exists(vd => hasFunctions(vd.getType, seen + adt.id)))
      case NAryType(tps, _) => tps.exists(hasFunctions(_, seen))
    }

    // The membership of `e` in `tpe`, where only refinements are checked
    def refinementsOf(e: Expr, tpe: Type): Expr = tpe match {
      case tpe: RefinementType =>
        val (base, preds) = typeOps.refinements(tpe, e)
        andJoin(refinementsOf(e, base) +: preds)
      case TupleType(tps) => andJoin(tps.zipWithIndex.map((tpe, i) => refinementsOf(TupleSelect(e, i + 1), tpe)))
      case SigmaType(params, to) =>
        // the components are the values of the bound variables, which the later types refer to
        val subst: Map[ValDef, Expr] = params.zipWithIndex.map((vd, i) => vd -> TupleSelect(e, i + 1)).toMap
        andJoin((params.map(_.tpe) :+ to).zipWithIndex.map((tpe, i) =>
          refinementsOf(TupleSelect(e, i + 1), typeOps.replaceFromSymbols(subst, tpe))))
      case _ => BooleanLiteral(true)
    }

    def isFirstOrder(tpe: Type): Boolean =
      !typeOps.exists { case _: FunctionType => true case _ => false } (tpe.getType)

    // The type `tpe` where every refinement only applies under `cond`, which is inhabited
    // whenever `tpe` is inhabited under `cond`
    def guardedType(cond: Expr, tpe: Type): Type = tpe match {
      case RefinementType(vd, pred) =>
        val nvd = vd.copy(tpe = guardedType(cond, vd.tpe))
        RefinementType(nvd, implies(cond, exprOps.replaceFromSymbols(Map(vd -> nvd.toVariable), pred)))
      case PiType(params, to) => PiType(params, guardedType(cond, to))
      case FunctionType(from, to) => FunctionType(from, guardedType(cond, to))
      case TupleType(tps) => TupleType(tps.map(guardedType(cond, _)))
      case SigmaType(params, to) =>
        // the later types refer to the bound variables at their guarded types
        val (nparams, subst) = params.foldLeft((Seq.empty[ValDef], Map.empty[ValDef, Expr])) {
          case ((nparams, subst), vd) =>
            val nvd = vd.copy(tpe = guardedType(cond, typeOps.replaceFromSymbols(subst, vd.tpe)))
            (nparams :+ nvd, subst + (vd -> nvd.toVariable))
        }
        SigmaType(nparams, guardedType(cond, typeOps.replaceFromSymbols(subst, to)))
      case _ => tpe
    }

    /* The default value of the model of a function, i.e. its value on the arguments the formula
     * doesn't apply it to. It must lie in the codomain `to` (in terms of `params`) for all arguments
     * in the domain, so a refined codomain is given by a call to a fresh uninterpreted function of
     * the parameters, whose result is in `{r: to | domain ==> r in to}`.
     * Function-typed parameters can't be checked by an expression, so they're assumed in the domain. */
    def defaultValue(params: Seq[ValDef], paramTypes: Seq[Type], to: Type): Option[Expr] =
      Option.when(to != to.getType) {
        val domain = andJoin((params zip paramTypes).collect {
          case (vd, tpe) if isFirstOrder(tpe) => refinementsOf(vd.toVariable, tpe)
        })
        exprOps.freshUninterpretedCall("default", params, guardedType(domain, to))
      }

    def extractFunction(f: Encoded, fullType: Type, seen: Map[FunctionType, Set[Encoded]]): Expr = {
      val tpe = fullType.getType.asInstanceOf[FunctionType]
      val nextSeen = seen + (tpe -> (seen(tpe) + f))
      extractedFunctions += tpe -> (extractedFunctions.getOrElse(tpe, Set.empty) + f)

      def extractLambda(f: Encoded, tpe: FunctionType): Option[Lambda] = {
        val optEqTemplate = templates.model.lambdaTemplates(tpe).find { tmpl =>
          wrapped.modelEval(tmpl.start, BooleanType()) == Some(BooleanLiteral(true)) &&
          modelEq(tmpl.ids._2, f)
        }

        optEqTemplate.map(templateLambda)
      }

      // The lambda of `tmpl` in the model, with the model values of its closure
      def templateLambda(tmpl: templates.LambdaTemplate): Lambda = {
        val localsSubst = tmpl.structure.locals.map { case (v, ev) =>
          v -> extractValue(ev, v.getType, nextSeen)
        }.toMap

        val res = exprOps.replaceFromSymbols(localsSubst, tmpl.structure.body)
        val (nl, subst) = normalizeStructure(res.asInstanceOf[Lambda], ast.SymbolOps.NormalizationLifting.Simple)
        exprOps.replaceFromSymbols(subst.map { case (v, e, _) => v -> e }.toMap, nl).asInstanceOf[Lambda]
      }

      // `lambda`, made structurally distinct from the functions that differ from `f` in the model:
      // the other extracted functions and the lambdas of the query. Lambdas are compared
      // structurally, up to the names of their parameters and locals (and to the values of their
      // closures, as with the lambdas of the query).
      def distinctFromOthers(lambda: Lambda): Lambda = {
        def normal(l: Lambda): Expr = {
          val (nl, subst) = normalizeStructure(l, ast.SymbolOps.NormalizationLifting.Simple)
          exprOps.replaceFromSymbols(subst.map { case (v, e, _) => v -> e }.toMap, nl)
        }

        lazy val taken = lambdaExtractions.collect {
          case (_, img: Lambda) if img.getType == lambda.getType => normal(img)
        }.toSet ++ templates.model.lambdaTemplates(tpe).filter { tmpl =>
          wrapped.modelEval(tmpl.start, BooleanType()) == Some(BooleanLiteral(true)) &&
          !modelEq(tmpl.ids._2, f)
        }.map(tmpl => normal(templateLambda(tmpl)))

        if (!taken(normal(lambda))) lambda else {
          val id = FreshIdentifier("f", true)
          closureExtractions :+= id -> lambda
          uniquateClosure(id, lambda)
        }
      }

      // The parameters of the model, and the parameter and result types of `fullType` in their terms
      val (params, paramTypes, resultType) = signature(fullType)

      // Whether the application of `caller` to `args` fails in the model (see [[Templates.appFailure]])
      def failsAt(caller: Encoded, ft: FunctionType, args: Seq[Encoded]): Boolean =
        templates.model.appFailureLiterals(ft).exists { case ((c, as), literal) =>
          modelEq(c, caller) && as.size == args.size && (as zip args).forall(modelEq(_, _)) &&
            wrapped.modelEval(literal, BooleanType()) == Some(BooleanLiteral(true))
        }
      def fails(args: Seq[Encoded]): Boolean = failsAt(f, tpe, args)

      // The model of the application of `f` to `args`, which fails where the application does
      def image(args: Seq[Encoded], resType: Type): Expr =
        if (fails(args)) Error(resType, "Application of a partial function")
        else extractValue(templates.mkApp(f, tpe, args), resType, nextSeen)

      // Results are extracted with their full types when these don't depend on the arguments
      val imageType = if ((typeOps.variablesOf(resultType) & params.map(_.toVariable).toSet).isEmpty) resultType
        else resultType.getType

      // Applications to distinguishing inputs come last, so that they don't determine the default
      // value of the extracted function (which must agree with quantifier instantiations).
      val arguments = templates.model.groundInstantiations(f, tpe).flatMap { case (b, eArgs) =>
        wrapped.modelEval(b, BooleanType()).filter(_ == BooleanLiteral(true)).map(_ => eArgs)
      }.distinct.sortBy(_.exists(templates.witnesses.isArgument))

      // Unless equality is intensional, a lambda can be equal to a function that it captures, such
      // as `() => f()` and `f`. The model of `f` is then that of its applications, as its lambda's
      // depends on it. Applications that lead back to `f` again then refer to it as to the other
      // functions being extracted.
      val inLambda = lambdasInProgress.exists(modelEq(f, _))
      val inCycle = inLambda && !capturedByTheirLambda.exists(modelEq(f, _))
      if (inCycle) capturedByTheirLambda :+= f
      val asLambda = if (inLambda) None else {
        lambdasInProgress :+= f
        val lambda = try extractLambda(f, tpe) finally lambdasInProgress = lambdasInProgress.init
        // the lambda of `f` applies its model, which is simpler
        lambda.map { l =>
          if (!capturedByTheirLambda.exists(modelEq(f, _))) l
          else lambdaExtractions.collectFirst { case (e, img) if img.getType == l.getType && modelEq(e, f) => img }.getOrElse(l)
        }
      }

      asLambda.orElse {
        if (!inCycle && seen(tpe).exists(e => modelEq(f, e))) {
          Some(functionExtractions.collectFirst { case (e, c) if modelEq(f, e) => c }.getOrElse {
            val c = UninterpretedCall(FreshIdentifier("x", true), Seq.empty, Seq.empty, FunctionType(Seq.empty, tpe))
            functionExtractions :+= f -> c
            c
          })
        } else {
          None
        }
      }.getOrElse {
        val res = if (arguments.isEmpty) {
          defaultValue(params, paramTypes, resultType).map(Lambda(params, _))
            .getOrElse(wrapped.modelEval(f, tpe).getOrThrow.asInstanceOf[Lambda])
        } else if (tpe.from.isEmpty) {
          val lambda = Lambda(Seq.empty, image(Seq.empty, imageType))
          lambdaExtractions.collectFirst {
            case (e, img) if img.getType == lambda.getType && modelEq(e, f) => img
          }.getOrElse(distinctFromOthers(lambda))
        } else {
          val projections: Map[Type, Encoded] = (arguments.head zip params)
            .groupBy(p => p._2.getType)
            .view.mapValues(_.head._1).toMap

          val exArguments = for (args <- arguments) yield {
            (params zip args).map { case (vd, arg) => extractValue(arg, vd.getType, nextSeen) }
          }

          /* The condition under which the `i`-th parameter `v` takes the model value `arg`.
           * Values that contain functions are told apart from the other values at that position
           * through the distinguishing inputs of their functions, so that the extracted function only
           * compares the results of applications, and never functions themselves. */
          def argumentCondition(v: ValDef, i: Int, arg: Encoded, exArg: Expr): Expr =
            if (!hasFunctions(v.getType)) Equals(v.toVariable, exArg) else {
              val others = arguments.map(_(i)).foldLeft(Seq.empty[Encoded]) { (acc, other) =>
                if (modelEq(other, arg) || acc.exists(modelEq(_, other))) acc else acc :+ other
              }
              val conds = others.map(other => separate(v.toVariable, v.getType, arg, other))
              if (conds.forall(_.isDefined)) andJoin(conds.flatten) else Equals(v.toVariable, exArg)
            }

          /* A test that holds when `x` is the model value `a`, and fails when it is `b`, if the model
           * has one that doesn't need comparing functions. `a` and `b` differ in the model. Functions
           * are tested on their distinguishing inputs, and datatypes on their constructors and fields. */
          def separate(x: Expr, tpe: Type, a: Encoded, b: Encoded): Option[Expr] = {
            // the first test among `parts` (lazily), trying those without functions first
            def firstOf(parts: Seq[(Type, Expr, Encoded, Encoded)]): Option[Expr] =
              parts.filterNot(p => modelEq(p._3, p._4)).sortBy(p => hasFunctions(p._1))
                .iterator.flatMap((tpe, x, a, b) => separate(x, tpe, a, b)).nextOption()

            tpe match {
              case _ if !hasFunctions(tpe) => Some(Equals(x, extractValue(a, tpe, nextSeen)))

              case ft: FunctionType =>
                // a distinguishing input may be one where only one of `a` and `b` fails
                val inputs = templates.witnesses.distinguishingInputs.collectFirst {
                  case ((f1, f2), (tpe, ws)) if tpe == ft &&
                    ((modelEq(f1, a) && modelEq(f2, b)) || (modelEq(f1, b) && modelEq(f2, a))) &&
                    (failsAt(a, ft, ws) || failsAt(b, ft, ws) ||
                      !modelEq(templates.mkApp(a, ft, ws), templates.mkApp(b, ft, ws))) => ws
                }

                // the pair may only have an on-demand distinguishing input, which we then request
                if (inputs.isEmpty) {
                  for ((tpe, ws) <- onDemandWitnesses if tpe == ft; (f1, f2, equality, depth) <- ws
                       if (modelEq(f1, a) && modelEq(f2, b)) || (modelEq(f1, b) && modelEq(f2, a))) {
                    requestedWitnesses += equality -> depth
                  }
                }

                // Applying `x` to an input where `a` or `b` fails would fail as well, so functions that
                // are told apart by where they fail are compared as such.
                inputs.filterNot(ws => failsAt(a, ft, ws) || failsAt(b, ft, ws)).flatMap { ws =>
                  val app = Application(x, (ws zip ft.from).map((w, tpe) => extractValue(w, tpe, nextSeen)))
                  separate(app, ft.to, templates.mkApp(a, ft, ws), templates.mkApp(b, ft, ws))
                }

              case TupleType(tps) =>
                val id = Variable.fresh("tuple", tpe)
                def select(v: Encoded, i: Int): Encoded = templates.mkEncoder(Map(id -> v))(TupleSelect(id, i))
                firstOf(tps.zipWithIndex.map((tpe, i) => (tpe, TupleSelect(x, i + 1), select(a, i + 1), select(b, i + 1))))

              case adt @ ADTType(_, tps) =>
                (wrapped.extractConstructor(a, adt), wrapped.extractConstructor(b, adt)) match {
                  case (Some(ca), Some(cb)) if ca != cb => Some(IsConstructor(x, ca))
                  case (Some(ca), Some(_)) =>
                    val id = Variable.fresh("adt", adt)
                    def select(v: Encoded, field: Identifier): Encoded =
                      templates.mkEncoder(Map(id -> v))(ADTSelector(id, field))
                    firstOf(getConstructor(ca, tps).fields.map { vd =>
                      (vd.getType, ADTSelector(x, vd.id), select(a, vd.id), select(b, vd.id))
                    }).map(cond => And(IsConstructor(x, ca), cond))
                  case _ => None
                }

              // sets, bags and maps of functions are compared as such
              case _ => None
            }
          }

          // Mappings on a subset of the arguments take the value at arbitrary other arguments, which
          // may lie outside of a refined codomain, so only exact mappings are kept for these.
          val optDefault = defaultValue(params, paramTypes, resultType)
          val subsets = if (optDefault.isDefined) Iterator(Set.empty[ValDef]) else params.toSet.subsets()

          // Exact mappings are extracted with the result type at their arguments
          val argumentsWithConds: Seq[(Seq[Encoded], Expr, Type)] =
            (for (subset <- subsets; (args, exArgs) <- arguments zip exArguments) yield {
              val (concreteArgs, condOpts) = params.zipWithIndex.map { case (v, i) =>
                if (!subset(v)) {
                  (args(i), Some(argumentCondition(v, i, args(i), exArgs(i))))
                } else {
                  (projections(v.getType), None)
                }
              }.unzip

              val resType = if (subset.isEmpty) typeOps.replaceFromSymbols((params zip exArgs).toMap, resultType)
                else imageType
              (concreteArgs, andJoin(condOpts.flatten), resType)
            }).toSeq

          val (withConds, default) = optDefault match {
            // all arguments agree in the model when one of them has a trivial condition
            // A trivial condition means that all arguments agree in the model, and that no
            // condition tells them apart without comparing functions. Outside of the domain, the
            // result needn't lie in the codomain, so it's only taken there.
            case Some(default) => argumentsWithConds.indexWhere(_._2 == BooleanLiteral(true)) match {
              case -1 => (argumentsWithConds, default)
              case i =>
                val (concreteArgs, _, resType) = argumentsWithConds(i)
                val domain = andJoin((params zip paramTypes).map((vd, tpe) => refinementsOf(vd.toVariable, tpe)))
                val inDomain = (params zip exArguments(i)).foldRight(domain) {
                  case ((vd, arg), body) => Let(vd, arg, body)
                }
                modelEvaluator.eval(inDomain, inox.Model.empty(targetProgram)).result match {
                  case Some(BooleanLiteral(false)) =>
                    (Seq((concreteArgs, Not(domain), resType)), default)
                  case _ =>
                    (Seq.empty, image(concreteArgs, resType))
                }
            }
            case None =>
              val withConds :+ ((concreteArgs, _, _)) = argumentsWithConds: @unchecked
              (withConds, image(concreteArgs, imageType))
          }

          // arguments whose conditions are trivial are covered by the default value. The first
          // argument of each condition is kept, in their order, so that the extracted function
          // doesn't depend on the hashes of the conditions.
          val sortedArguments = withConds
            .filter(_._2 != BooleanLiteral(true))
            .foldLeft(VectorMap.empty[Expr, (Seq[Encoded], Expr, Type)]) { (m, p) =>
              if (m contains p._2) m else m + (p._2 -> p)
            }
            .toSeq
            .sortBy(p => -exprOps.formulaSize(p._1))

          val mappings = sortedArguments.map { case (cond, (arguments, _, resType)) =>
            (cond, image(arguments, resType))
          }

          val lambda = Lambda(params, mappings.foldRight(default) {
            case ((cond, img), elze) => IfExpr(cond, img, elze)
          })

          lambdaExtractions.collectFirst {
            case (e, img) if img.getType == lambda.getType && modelEq(e, f) => img
          }.getOrElse(distinctFromOthers(lambda))
        }

        lambdaExtractions :+= f -> res
        res
      }
    }

    /* The solver may return values that cannot be decoded by the theory encoder if they
     * weren't constrained by the generated clauses (eg. default values for functions).
     * We replace these by `simplestValue` instead of crashing as they won't have any influence
     * on model evaluation. */
    def decodeOrSimplest(e: t.Expr): s.Expr = try {
      decode(e)
    } catch {
      case t: TheoryException => program.symbols.simplestValue(decode(e.getType))
    }

    val initSeen: Map[FunctionType, Set[Encoded]] = Map.empty.withDefaultValue(Set.empty)
    val exModel = wrapped.getModel((e, tpe) => decodeOrSimplest(extractValue(e, encode(tpe), initSeen)))
    // The constants that stand for functions are given by these functions
    val exFunctions = functionExtractions.map { case (e, c) =>
      c -> lambdaExtractions.collectFirst {
        case (f, lambda) if lambda.getType == c.getType && modelEq(f, e) => lambda
      }.get
    }
    val interpretations = exFunctions.map(p => (p._1.id, Seq.empty[s.Type]) -> decodeOrSimplest(Lambda(Seq.empty, p._2))) ++
      closureExtractions.map(p => (p._1, Seq.empty[s.Type]) -> decodeOrSimplest(p._2))

    // The distinct functions of the model need a distinguishing input, so on-demand pairs join the
    // regular unfolding once they show up in it (see [[LambdaTemplates.onDemandWitnesses]]): a free
    // function with the other free functions of the model, and with the lambdas that the model
    // instantiates. Pairs of lambdas are left to the extraction of the functions they are passed to
    // (see `argumentCondition`). We don't ask the model whether the functions are distinct, as solvers
    // may evaluate the equality of function values extensionally: their unfolding is guarded by it.
    for {
      (tpe, ws) <- onDemandWitnesses
      fs <- extractedFunctions.get(tpe).toSeq
      lambdas = templates.model.lambdaTemplates(tpe).map(tmpl => tmpl.ids._2 -> tmpl.start).toMap
      (f1, f2, equality, _) <- ws
      if !lambdas.contains(f1) && fs.exists(modelEq(_, f1)) && (lambdas.get(f2) match {
        case Some(start) => wrapped.modelEval(start, BooleanType()) == Some(BooleanLiteral(true))
        case None => fs.exists(modelEq(_, f2))
      })
    } exposedWitnesses += equality

    inox.Model(program)(exModel.vars, exModel.interpretations ++ interpretations)
  }

  protected val emptyModel: Model =
    inox.Model(program)(Map.empty, Map.empty)

  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] =
      context.timers.solvers.unrolling.run(scala.util.Try({

    unrollBoundHit = false

    // throw error immediately if a previous call has already failed
    if (failures.nonEmpty) throw failures.head

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

    new Check[config.type](config, assumptions).run()
  }).recover {
    case e @ (_: InternalSolverError | _: Unsupported) =>
      if (reporter.isDebugEnabled) reporter.debug(e)
      else if (!silentErrors && !abort) reporter.error(e.getMessage)
      config.cast(Unknown)
  }.get)

  /** A single call to [[checkAssumptions]]: a state machine that alternates between checking the
    * current unfolding, extracting and validating models, and unrolling further.
    *
    * Each state has its own method, which returns the next state, until a [[CheckResult]] is reached:
    *  - [[modelCheck]] looks for a model of the current unfolding, with the blockers assumed false,
    *  - [[finiteRangeCheck]] checks the models of queries over finite ranges,
    *  - [[validate]] extracts a model and checks it against the assumptions,
    *  - [[instantiateQuantifiers]] promotes the pending quantifier instantiations,
    *  - [[proofCheck]] checks the query without the blockers, to prove it unsatisfiable,
    *  - [[unroll]] unfolds the next generation of blockers.
    */
  private class Check[C <: Configuration & Singleton](val config: C, assumptions: Set[Expr]) {
    import SolverResponses._

    private type Response = SolverResponse[underlying.Model, Set[underlying.Trees]]

    private val assumptionsSeq       : Seq[Expr]          = assumptions.toSeq
    private val encodedAssumptions   : Seq[Encoded]       = assumptionsSeq.map { expr =>
      val vars = exprOps.variablesOf(expr)
      templates.mkEncoder(vars.map(v => encode(v) -> freeVars(v)).toMap)(encode(expr))
    }
    private val encodedToAssumptions : Map[Encoded, Expr] = (encodedAssumptions zip assumptionsSeq).toMap

    private def decodeAssumptions(core: Set[Encoded]): Set[Expr] = {
      core.flatMap(ast => encodedToAssumptions.get(ast) match {
        case Some(n @ Not(_: Variable)) => Some(n)
        case Some(v: Variable) => Some(v)
        case _ => None
      })
    }

    // the lambdas and the functions they capture that the model makes equal, and that the unrolling
    // hasn't related yet (see [[LambdaTemplates.equalCaptures]])
    private var modelCaptures: Option[(underlying.Model, Seq[(Encoded, Encoded)])] = None
    private def equalCaptures(umodel: underlying.Model): Seq[(Encoded, Encoded)] = modelCaptures match {
      case Some((m, captures)) if m.asInstanceOf[AnyRef] eq umodel.asInstanceOf[AnyRef] => captures
      case _ =>
        val candidates = templates.model.equalCaptures
        val captures = if (candidates.isEmpty) Seq.empty else {
          val wrapped = wrapModel(umodel)
          def holds(e: Encoded): Boolean = wrapped.modelEval(e, t.BooleanType()) == Some(t.BooleanLiteral(true))
          candidates.collect { case (start, lambda, f) if holds(start) && holds(templates.mkEquals(lambda, f)) => lambda -> f }
        }
        modelCaptures = Some(umodel -> captures)
        captures
    }

    /** Checks the underlying solver under `assumptions`. With proofs, a check whose answer can be
      * that of the solver (`refutes`) asks the underlying solver for its proof, and its unsat
      * answer comes with the certificate of the check (see [[certify]]). */
    private def checkUnderlying(config: Configuration, refutes: Boolean = false)(assumptions: Set[Encoded]): Response = {
      val proving = producesProofs && this.config.withProof && refutes
      underlying.checkAssumptions(if (proving) config `max` Proof else config)(assumptions) match {
        case UnsatWithProof(proof) => UnsatWithProof(certify(assumptions.toSeq, proof, encodedAssumptions.toSet))
        case response => response
      }
    }

    sealed abstract class CheckState
    class CheckResult(val response: config.Response[Model, Assumptions]) extends CheckState
    case class Validate(model: underlying.Model) extends CheckState
    case object ModelCheck extends CheckState
    case object FiniteRangeCheck extends CheckState
    case object InstantiateQuantifiers extends CheckState
    case object ProofCheck extends CheckState
    case object Unroll extends CheckState

    object CheckResult {
      def cast(resp: Response): CheckResult = {
        // unsat assumptions may have been requested internally (eg. for witness assumptions), and
        // with proofs, an unsat answer comes with its certificate (see [[checkUnderlying]])
        val res = resp match {
          case UnsatWithProof(_) if config.withProof => resp
          case UnsatWithAssumptions(_) if config.withProof && producesProofs =>
            UnsatWithProof(Left("the check that refuted the query asks for its unsat assumptions, which a proof doesn't come with"))
          case _: Unsatisfiable if config.withProof && producesProofs =>
            UnsatWithProof(Left("the check that refuted the query has no proof"))
          case _: Unsatisfiable if !config.withUnsatAssumptions => Unsat
          case _ => resp
        }
        CheckResult(config.convert(config.cast(res), extractSimpleModel, decodeAssumptions))
      }

      def apply[M <: Model, A <: Assumptions](resp: config.Response[M, A]): CheckResult = resp match {
        case SatWithModel(_) if !checkModels && abort => new CheckResult(config `cast` Unknown)
        case _ => new CheckResult(resp)
      }

      def unapply(res: CheckResult): Option[config.Response[Model, Assumptions]] = Some(res.response)
    }

    object Abort {
      def unapply[A,B](resp: SolverResponse[A,B]): Boolean = {
        if (failures.nonEmpty || abort) {
          true
        } else if (resp == Unknown) {
          if (!silentErrors) {
            reporter.error("Something went wrong. Underlying solver returned Unknown.")
          }
          true
        } else {
          false
        }
      }
    }

    private var unrollCount: Int = 0

    private def canUnroll: Boolean = unrollBound < 0 || unrollCount < unrollBound

    // The depth up to which distinguishing inputs are instantiated: 0 until the first model is found,
    // then one more level with each unrolling (see [[LambdaTemplates.witnessEqualities]])
    private var witnessLevel: Int = 0

    def run(): config.Response[Model, Assumptions] = {
      var currentState: CheckState = ModelCheck
      while (!currentState.isInstanceOf[CheckResult]) {
        currentState = currentState match {
          case ModelCheck => modelCheck()
          case FiniteRangeCheck => finiteRangeCheck()
          case Validate(umodel) => validate(umodel)
          case InstantiateQuantifiers => instantiateQuantifiers()
          case ProofCheck => proofCheck()
          case Unroll => unroll()
          case otherwise => sys.error(s"Unexpected case: $otherwise")
        }
      }

      val CheckResult(res) = currentState: @unchecked
      res match {
        case _: Unsatisfiable => templates.checkRefutation(lastCheck, encodedAssumptions.toSet)
        case _ =>
      }
      res
    }

    /** The assumptions of the last check of the underlying solver, or `None` if it had clauses of
      * its own, which an unsatisfiable answer comes from (see [[RuleChecker.checkRefutation]]). */
    private var lastCheck: Option[Set[Encoded]] = None

    /** Records `assumptions` as those of the next check of the underlying solver. */
    private def checking(assumptions: Set[Encoded]): Set[Encoded] = {
      lastCheck = Some(assumptions)
      assumptions
    }

    /** `model`, extracted from `umodel`, with the type parameters whose flags are off in `umodel`
      * instantiated with the empty type. The model checks only assume that type parameters have
      * values until a guard lets them be empty (see [[TypeTemplates.satisfactionAssumptions]]),
      * and from then on, the values of a type parameter that the model holds imply its flag. The
      * values of the model have the instantiated types, and the values of an empty type parameter
      * that the extracted model may still hold where nothing reaches them, such as the default
      * results of functions into it, become errors. */
    private def withEmptyTypes(model: program.Model, umodel: underlying.Model): program.Model = {
      val flags = templates.model.typeParameterFlags
      val emptyTypes = if (flags.isEmpty) Set.empty else {
        val wrapped = wrapModel(umodel)
        flags.collect {
          case (tp, flag) if wrapped.modelEval(flag, t.BooleanType()) == Some(t.BooleanLiteral(false)) =>
            decode(tp.asInstanceOf[t.Type])
        }.collect { case tp: TypeParameter => tp }
      }
      if (emptyTypes.isEmpty) model else {
        val empty: Type = RefinementType(ValDef.fresh("empty", UnitType()), BooleanLiteral(false))
        val types: Map[TypeParameter, Type] = emptyTypes.map(_ -> empty).toMap
        def inst(tpe: Type): Type = typeOps.instantiateType(tpe, types)
        def instValue(e: Expr): Expr = typeOps.instantiateType(exprOps.postMap {
          case GenericValue(tp, _) if types.contains(tp) => Some(Error(tp, "Value of the empty type " + tp.id.name))
          case _ => None
        } (e), types)
        inox.Model(program)(
          model.vars.map { case (vd, e) => vd.copy(tpe = inst(vd.tpe)) -> instValue(e) },
          model.interpretations.map { case ((id, tps), e) => (id, tps.map(inst)) -> instValue(e) },
          types)
      }
    }

    private def witnessEqualities: Map[Encoded, Int] =
      if (witnessLevel > 0) templates.witnesses.equalities else Map.empty

    /** The literals that keep apart the lambdas that earlier models made equal, which the model
      * checks assume along with the equalities (see [[WitnessTemplates.lambdaDistinctions]]). An
      * unsatisfiable check under them is handled as one under the equalities: the decisions are
      * made on a check without either. */
    private def lambdaDistinctions: Set[Encoded] = templates.witnesses.distinctions

    /* The equalities between functions without distinguishing inputs that appear in the unsat core
     * of `res`, or all of them if the solver gave no core. Cores aren't necessarily reported as
     * literals, so they are compared modulo negation. */
    private def coreEqualities(res: Response, equalities: Map[Encoded, Int]): Map[Encoded, Int] = res match {
      case _: Unsatisfiable if equalities.nonEmpty =>
        def atom(e: Encoded): Encoded = templates.extractNot(e).getOrElse(e)
        res match {
          case UnsatWithAssumptions(core) =>
            val atoms = core.map(atom)
            equalities.filter(p => atoms(atom(p._1)))
          case _ => equalities
        }
      case _ => Map.empty
    }

    /* Instantiates the distinguishing inputs of the given equalities up to the current witness level.
     * If they are all deeper, we move on to the proof check: it either proves the query, or leads to
     * an unrolling, which raises the level. Going through the proof check ensures that witnesses can't
     * delay a proof that the unfolding already allows (see `function-witnesses.md`). */
    private def instantiateWitnesses(needed: Map[Encoded, Int]): CheckState = {
      val current = needed.filter(_._2 <= witnessLevel).keySet
      if (current.nonEmpty) {
        reporter.debug(" - Instantiating distinguishing function inputs")
        for (cl <- templates.witnesses.instantiate(current)) {
          assertClause(cl)
        }
        ModelCheck
      } else {
        ProofCheck
      }
    }

    /* Decides what to do with the pending equalities when a check that assumed them is UNSAT, given
     * the core equalities of the check and a way to run it again without the equalities. Returns
     * the next state, or the result of the check without equalities when they aren't to blame.
     *
     * Equalities in the core are instantiated first. Otherwise, the core may still be missing them
     * (solvers don't reliably report every assumption they used), so we check again without them:
     * if that is satisfiable, the equalities are needed, and we instantiate the whole current level,
     * which also keeps instantiation fair. */
    private def blamedEqualities(
      inCore: Map[Encoded, Int],
      equalities: Map[Encoded, Int],
      withoutEqualities: => Response
    ): Either[CheckState, Response] = {
      if (inCore.exists(_._2 <= witnessLevel)) {
        Left(instantiateWitnesses(inCore))
      } else {
        reporter.debug(" - Checking again without equalities between functions")
        val res = withoutEqualities
        res match {
          case _: Satisfiable => Left(instantiateWitnesses(equalities))
          case _ => Right(res)
        }
      }
    }

    /** Checks the current unfolding with the blockers assumed false (along with the other
      * satisfaction assumptions): a model of it is a candidate model of the query. */
    private def modelCheck(): CheckState = {
      reporter.debug(" - Running search...")

      val equalities = witnessEqualities
      val distinctions = lambdaDistinctions
      val getModel = !templates.quantifiers.requiresFiniteRangeCheck || checkModels || templates.quantifiers.hasAxioms || config.withModel
      val getAssumptions = (unrollAssumptions && templates.unfolding.canUnroll) || config.withUnsatAssumptions

      // the check without equalities doesn't ask for unsat assumptions for them, so that it can
      // ask for a proof
      def check(equalities: Iterable[Encoded]): Response =
        context.timers.solvers.unrolling.check.run {
          // the lambdas that a model makes equal are checked even when models are ignored
          val model = (getModel && !ignoreModels) || templates.witnesses.hasLambdaPairs
          val checkConfig = Configuration(model = model, unsatAssumptions = getAssumptions || equalities.nonEmpty)
          // its unsat answer is that of the solver once nothing is left to unroll or to assume
          val refutes = !templates.unfolding.canUnroll && templates.unfolding.satisfactionAssumptions.isEmpty
          checkUnderlying(checkConfig, refutes)(
            checking(ListSet.from(encodedAssumptions) ++ templates.unfolding.satisfactionAssumptions ++ equalities)
          )
        }

      val resWithEqualities = check(equalities.keys ++ distinctions)

      reporter.debug(" - Finished search with blocked literals")

      // the equalities are only assumed in `resWithEqualities`, so that every UNSAT answer below
      // comes from a check without them
      val next: Either[CheckState, Response] = resWithEqualities match {
        case Abort() => Right(resWithEqualities)
        case _: Unsatisfiable if equalities.nonEmpty || distinctions.nonEmpty =>
          blamedEqualities(coreEqualities(resWithEqualities, equalities), equalities, check(Seq.empty))
        case _ => Right(resWithEqualities)
      }

      next match {
        case Left(state) => state
        case Right(res) => res match {
          case Abort() =>
            CheckResult.cast(Unknown)

          // distinguishing inputs only matter once we have a model, in which distinct functions
          // may still agree on every input: check again with these assumed equal
          case _: Satisfiable if witnessLevel == 0 && templates.witnesses.equalities.nonEmpty =>
            witnessLevel = 1
            ModelCheck

          case _: Satisfiable if templates.quantifiers.requiresFiniteRangeCheck =>
            FiniteRangeCheck

          // the model was only requested to check the lambdas that it makes equal (see [[validate]])
          case SatWithModel(model) if !getModel || ignoreModels =>
            if (decideEquatedLambdas(model)) ModelCheck
            else if (config.withModel) CheckResult(config.cast(SatWithModel(emptyModel)))
            else CheckResult.cast(Sat)

          case Sat =>
            if (config.withModel && ignoreModels) then
              // did we discard the model check manually?
              // if yes, recast to the right response, with an empty model
              CheckResult(config.cast(SatWithModel(emptyModel)))
            else
              CheckResult.cast(Sat)

          case SatWithModel(model) =>
            Validate(model)

          // Satisfaction assumptions that remain once nothing can be unrolled
          // (such as type parameters being inhabited) must still be dropped
          // before the query can be deemed unsatisfiable.
          case _: Unsatisfiable if !templates.unfolding.canUnroll && templates.unfolding.satisfactionAssumptions.isEmpty =>
            CheckResult.cast(res)

          case UnsatWithAssumptions(assumptions) if unrollAssumptions =>
            for (b <- assumptions) templates.unfolding.promoteBlocker(b)
            ProofCheck

          case _ =>
            ProofCheck
        }
      }
    }

    /** Checks the current unfolding along with the clauses that bound the ranges of the
      * finite-range types, to get a model that respects them. */
    private def finiteRangeCheck(): CheckState = {
      reporter.debug(" - Verifying finite ranges")

      val clauses = templates.quantifiers.finiteRangeClauses

      // the model must have distinguishing inputs as well (see [[modelCheck]])
      val equalities = witnessEqualities
      val distinctions = lambdaDistinctions

      val next: Either[CheckState, Response] =
        context.timers.solvers.unrolling.check.run {
          pushUnderlying()
          for (cl <- encodedAssumptions.toSeq ++ templates.unfolding.satisfactionAssumptions ++ clauses) {
            assertUnderlying(cl)
          }
          def check(equalities: Iterable[Encoded]) = {
            lastCheck = None
            checkUnderlying(Configuration(model = true, unsatAssumptions = equalities.nonEmpty))(
              equalities.toSet
            )
          }
          val res = check(equalities.keys ++ distinctions)
          val next = res match {
            case _: Unsatisfiable if (equalities.nonEmpty || distinctions.nonEmpty) && !abort =>
              val inCore = coreEqualities(res, equalities).filter(_._2 <= witnessLevel)
              if (inCore.nonEmpty) Left(inCore)
              else check(Seq.empty) match {
                case _: Satisfiable => Left(equalities.filter(_._2 <= witnessLevel))
                case _ => Right(res)
              }
            case _ => Right(res)
          }
          popUnderlying()
          next.left.map { needed =>
            if (needed.nonEmpty) instantiateWitnesses(needed) else InstantiateQuantifiers
          }
        }

      reporter.debug(" - Finished checking finite ranges")

      next match {
        case Left(state) => state
        case Right(res) => res match {
          case Abort() =>
            CheckResult.cast(Unknown)

          case SatWithModel(model) =>
            Validate(model)

          case _ =>
            InstantiateQuantifiers
        }
      }
    }

    /** Decides the equality of the lambdas that `umodel` makes equal although their equality doesn't
      * follow from their structure, by comparing their bodies (see [[WitnessTemplates.lambdaComparison]]):
      *  - if no solution makes the bodies differ on some input, the lambdas are extensionally equal,
      *    and the models may keep them equal;
      *  - if no solution with the values that `umodel` gives their captures does, this model may
      *    keep them equal;
      *  - otherwise, they are applied to an input on which their bodies differ with these captures,
      *    so that the model can't keep them equal. Once per round of the unfolding, after which the
      *    model checks keep them apart until the next round, so that each round stays finite (see
      *    [[unroll]]).
      * Returns whether `umodel` is discarded, which is when it can't keep some of them equal. */
    private def decideEquatedLambdas(umodel: underlying.Model): Boolean = {
      val wrapped = wrapModel(umodel)
      val pairs = templates.witnesses.equatedLambdas(
        e => wrapped.modelEval(e, t.BooleanType()) == Some(t.BooleanLiteral(true)))
      var discarded = false
      for (p <- pairs if !abort) {
        reporter.debug(" - Comparing the bodies of lambdas that the model makes equal")
        // the captures that may contain functions are left out: their encodings in a model aren't values
        lazy val fixed = fixedCaptures(templates.witnesses.captures(p).collect {
          case (c, tpe) if !FunctionEquality.containsFunctions(programEncoder.targetProgram)(tpe) => c -> tpe
        }.flatMap((c, tpe) => wrapped.modelEval(c, tpe).map(c -> _)))
        if (!agreeEverywhere(p) && (fixed.isEmpty || !agreeWith(p, fixed))) {
          discarded = true
          if (!templates.witnesses.canProbe(p) || !probe(p, fixed)) {
            for (cl <- templates.witnesses.keepApart(p)) assertClause(cl)
          }
        }
      }
      discarded || abort
    }

    /** Checks under the comparison of the bodies of the lambdas of `p` (see [[Templates.instantiateComparison]])
      * and under `extra`, with the given unfolding assumptions. */
    private def checkComparison(p: templates.witnesses.LambdaPair, extra: Set[Encoded], refuting: Boolean): Response = {
      val (literal, _, clauses) = templates.witnesses.comparison(p)
      for (cl <- clauses) assertClause(cl)
      val unfolding = if (refuting) templates.unfolding.refutationAssumptions else templates.unfolding.satisfactionAssumptions
      context.timers.solvers.unrolling.check.run {
        checkUnderlying(Configuration(model = !refuting, unsatAssumptions = false))(
          ListSet.from(encodedAssumptions) ++ unfolding ++ extra + literal)
      }
    }

    /** Whether the bodies of the lambdas of `p` agree on every input in every solution: the check
      * under their comparison is a refutation, as in the proof check. If so, the models may keep
      * them equal. */
    private def agreeEverywhere(p: templates.witnesses.LambdaPair): Boolean =
      checkComparison(p, Set.empty, refuting = true) match {
        case _: Unsatisfiable =>
          reporter.debug(" - The lambdas agree on every input")
          templates.witnesses.markEqual(p)
          true
        case _ => false
      }

    /** The literal under which the captures of a pair of lambdas have the given values, if any. */
    private def fixedCaptures(captures: Seq[(Encoded, t.Expr)]): Set[Encoded] =
      if (captures.isEmpty) Set.empty else {
        val (fixed, clauses) = templates.witnesses.fixCaptures(captures)
        for (cl <- clauses) assertClause(cl)
        Set(fixed)
      }

    /** Whether the bodies of the lambdas of `p` agree on every input when their captures have the
      * values of a model, under `fixed` (see [[fixedCaptures]]): if so, the model may keep them equal. */
    private def agreeWith(p: templates.witnesses.LambdaPair, fixed: Set[Encoded]): Boolean =
      !abort && (checkComparison(p, fixed, refuting = true) match {
        // the values of the model must be consistent with the unfolding when they are fixed: as the
        // model satisfies it, they are unless their encoding differs from the model's own values,
        // and the check would then hold whatever the bodies
        case _: Unsatisfiable if !abort && !checkUnderlying(Configuration(model = false, unsatAssumptions = false))(
            ListSet.from(encodedAssumptions) ++ templates.unfolding.refutationAssumptions ++ fixed).isInstanceOf[Unsatisfiable] =>
          reporter.debug(" - The lambdas agree on every input with the captures of the model")
          true
        case _ => false
      })

    /** Applies the lambdas of `p` to an input on which their bodies differ when their captures have the
      * values of a model, under `fixed`, if a model of their comparison gives one (see
      * [[WitnessTemplates.probeLambdas]]). Returns whether it did. */
    private def probe(p: templates.witnesses.LambdaPair, fixed: Set[Encoded]): Boolean =
      !abort && (checkComparison(p, fixed, refuting = false) match {
        case SatWithModel(model) =>
          val (_, args, _) = templates.witnesses.comparison(p)
          val input = new ProbeInput(wrapModel(model), templates.witnesses.captures(p))
          val values = (args zip p.t1.tpe.from).map(input.value(_, _))
          if (!values.forall(_.isDefined)) reporter.debug(" - The model gives no input that can be probed")
          values.forall(_.isDefined) && {
            reporter.debug(" - The lambdas differ on " + values.flatten.mkString(", "))
            for (cl <- templates.witnesses.probe(p, values.flatten, input.terms)) assertClause(cl)
            true
          }
        case _ => false
      })

    /** The inputs of a comparison in its model `wrapped`, as expressions that the unfolding can apply
      * the compared lambdas to (see [[probe]]):
      *  - a function, wherever it occurs in an input (in the fields of a value, in the results of
      *    another function, ...), is given by a fresh lambda that captures nothing, with the values
      *    that the model gives it on the inputs that the unfolding applies it to.
      *    That is enough to tell the bodies apart, which can only observe it through these
      *    applications, and the model's own function (from its extraction) may call fresh functions;
      *  - the values of abstract types (type parameters, uninterpreted sorts) can't be encoded as
      *    values, so they are given by the captures of the lambdas that have them in the model, which
      *    the bodies compare them to (see [[terms]]).
      * Applications to functions are given the applied terms, which the fresh lambda compares
      * extensionally to its arguments. None for an input that contains functions elsewhere (in sets,
      * maps, ...), or nested more than `maxDepth` times in the results of other functions, as with
      * the functions in a stream. */
    private class ProbeInput(wrapped: ModelWrapper, captures: Seq[(Encoded, t.Type)]) {
      import programEncoder.targetProgram.symbols.{given, _}

      private val maxDepth = 8
      private val abstractTerms = scala.collection.mutable.Map.empty[t.GenericValue, Option[t.Variable]]
      private var bound = Map.empty[t.Variable, Encoded]

      /** The encoded terms that the free variables of the inputs stand for. */
      def terms: Map[t.Variable, Encoded] = bound

      private def abstractTerm(gv: t.GenericValue): Option[t.Variable] = abstractTerms.getOrElseUpdate(gv,
        captures.collectFirst { case (e, tpe) if tpe == gv.tp && wrapped.modelEval(e, tpe) == Some(gv) => termOf(e, tpe) })

      /** A variable that stands for the encoded term `e` of type `tpe`. */
      private def termOf(e: Encoded, tpe: t.Type): t.Variable = {
        val v = t.Variable.fresh("v", tpe, true)
        bound += v -> e
        v
      }

      /** `value`, a value of the model without functions, with its abstract values replaced by the
        * terms that have them. */
      private def ground(value: t.Expr): Option[t.Expr] = {
        var ok = true
        val res = t.exprOps.postMap {
          case gv: t.GenericValue =>
            val v = abstractTerm(gv)
            if (v.isEmpty) ok = false
            v
          case _ => None
        }(value)
        Option.when(ok && closed(res) && !t.exprOps.exists { case _: t.Lambda | _: t.Error => true; case _ => false }(res))(res)
      }

      /** Whether `e` is a closed expression over the program and the terms. */
      private def closed(e: t.Expr): Boolean =
        (t.exprOps.variablesOf(e) -- bound.keySet).isEmpty && !t.exprOps.exists {
          case _: t.GenericValue => true
          case fi: t.FunctionInvocation => lookupFunction(fi.id).isEmpty
          case _ => false
        }(e)

      private def holds(e: Encoded): Boolean = wrapped.modelEval(e, t.BooleanType()) == Some(t.BooleanLiteral(true))

      /** The value of the comparison argument `a` of type `tpe`. */
      def value(a: Encoded, tpe: t.Type): Option[t.Expr] = {
        val v = t.Variable.fresh("w", tpe, true)
        // the values may refer to the terms of abstract values
        build(v, tpe, e => templates.mkEncoder(bound + (v -> a))(e), maxDepth)
      }

      /** The value of `term` of type `tpe`, given the encoding of the terms over the argument. */
      private def build(term: t.Expr, tpe: t.Type, encode: t.Expr => Encoded, depth: Int): Option[t.Expr] = {
        def hasFunctions(tpe: t.Type) = FunctionEquality.containsFunctions(programEncoder.targetProgram)(tpe)
        def eval(term: t.Expr, tpe: t.Type) = wrapped.modelEval(encode(term), tpe)
        tpe.getType match {
          case tpe if !hasFunctions(tpe) => eval(term, tpe).flatMap(ground)

          case ft @ t.FunctionType(from, to) if depth > 0 =>
            val c = encode(term)
            def same(x: Encoded, y: Encoded) = holds(templates.mkEquals(x, y))
            // the applications of the function in the model
            val applied = templates.model.applications(ft).collect { case (b, caller, as) if holds(b) && same(caller, c) => as }
            // the applications of the argument that fail in the model, which the lambda then fails on
            def fails(as: Seq[Encoded]) = templates.model.appFailureLiterals(ft).exists { case ((caller, cas), literal) =>
              same(caller, c) && cas.size == as.size && (cas zip as).forall(same) && holds(literal)
            }
            // the arguments are values where they can be, and the applied terms otherwise (functions,
            // which the lambda then compares extensionally)
            val points = applied.map { as =>
              (as zip from).map((e, tpe) => wrapped.modelEval(e, tpe).flatMap(ground).orElse(Some(termOf(e, tpe)))) -> fails(as)
            }.distinctBy(_._1)
            Option.when(points.forall(_._1.forall(_.isDefined))) {
              val results = points.map { (as, failing) =>
                if (failing) Some(t.Error(to, "Application of a partial function"))
                else build(t.Application(term, as.map(_.get)), to, encode, depth - 1)
              }
              // the value outside of the points must lie in `to`, as do the results
              val default = (points zip results).collectFirst { case ((_, false), Some(r)) => r }
                .orElse(Option.when(to == to.getType)(simplestValue(to)).filter(closed))
              Option.when(default.isDefined && results.forall(_.isDefined)) {
                val params = from.map(tpe => t.ValDef.fresh("x", tpe, true))
                (points zip results).foldRight(default.get) { case (((as, _), r), elze) =>
                  t.IfExpr(t.andJoin((params zip as).map((vd, v) => t.Equals(vd.toVariable, v.get))), r.get, elze)
                } match { case body => t.Lambda(params, body) }
              }
            }.flatten

          // past the depth, the function is only known to lie in its type
          case ft: t.FunctionType if ft == ft.getType =>
            Some(simplestValue(ft)).filter(closed)

          case t.TupleType(tps) =>
            val elems = tps.indices.map(i => build(t.TupleSelect(term, i + 1), tps(i), encode, depth))
            Option.when(elems.forall(_.isDefined))(t.Tuple(elems.map(_.get)))

          case adt: t.ADTType => eval(term, adt) match {
            case Some(t.ADT(id, tps, _)) =>
              val cons = getConstructor(id, tps)
              // the fields of the constructor that the model gives the value
              val inCons = t.IsConstructor(term, id)
              val fields = cons.fields.map(vd => build(t.ADTSelector(term, vd.id), vd.getType, encode, depth))
              Option.when(holds(encode(inCons)) && fields.forall(_.isDefined))(t.ADT(id, tps, fields.map(_.get)))
            case _ => None
          }

          case _ => None
        }
      }
    }

    /** Extracts a model from `umodel` and validates it, once the unfolding has related the lambdas
      * of `umodel` to the functions they capture. */
    private def validate(umodel: underlying.Model): CheckState = {
      if (abort) {
        // Extracting and validating a large model takes time: skip them once interrupted
        CheckResult.cast(Unknown)
      } else if (templates.witnesses.hasLambdaPairs && decideEquatedLambdas(umodel)) {
        // under extensional equality, the model made lambdas equal whose bodies we had to compare
        // (see [[WitnessTemplates.lambdaDistinctions]]), so we look for a model again
        ModelCheck
      } else if (equalCaptures(umodel).nonEmpty) {
        // the unrolling left out the clauses that relate these lambdas to the functions they capture
        // (see [[LambdaTemplates.equalCaptures]]), so the model needs them before it can be trusted
        reporter.debug(" - Relating lambdas to the captured functions that the model makes equal")
        for ((lambda, f) <- equalCaptures(umodel); cl <- templates.model.relateCapture(lambda, f)) {
          assertClause(cl)
        }
        // the applications of the functions are then related to the lambdas by unrolling them
        if (templates.unfolding.canUnroll) Unroll else ModelCheck
      } else {
        requestedWitnesses = Map.empty
        exposedWitnesses = Set.empty
        (try { Some(withEmptyTypes(extractTotalModel(umodel), umodel)) } catch {
          case NoSimpleValue(tpe) =>
            if (!silentErrors) {
              reporter.error("No simple value found for type " + tpe.asString)
            }
            None
          case Canceled() => None
        }).map(validateExtracted(umodel, _)).getOrElse(CheckResult `cast` Unknown)
      }
    }

    /** Validates `model`, extracted from `umodel`: its functions may first need their
      * distinguishing inputs, and its quantifiers must fit in the supported fragment. */
    private def validateExtracted(umodel: underlying.Model, model: Model): CheckState = {
      lazy val sat = CheckResult(config `cast` (if (config.withModel) SatWithModel(model) else Sat))
      lazy val unknown = CheckResult `cast` Unknown

      lazy val valid = !checkModels || validateModel(model, assumptionsSeq, silenceErrors = silentErrors)

      // the extracted functions need these distinguishing inputs to tell their arguments apart,
      // and they are unfolded fairly, like the others (see [[LambdaTemplates.witnessEqualities]])
      val requested = requestedWitnesses.filter(_._2 <= (witnessLevel max 1)).keySet
      if (requested.nonEmpty && !abort) {
        reporter.debug(" - Instantiating requested distinguishing function inputs")
        for (cl <- templates.witnesses.instantiate(requested)) {
          assertClause(cl)
        }
        ModelCheck
      } else if (requestedWitnesses.nonEmpty && functionEquality == FunctionEquality.None && !abort) {
        // Without function equality, the model can't compare the functions instead, so we wait
        // for the unfolding to reach their distinguishing inputs (see [[instantiateWitnesses]]).
        reporter.debug(" - Requested distinguishing function inputs are deeper than the unfolding")
        witnessLevel = witnessLevel max 1
        ProofCheck
      } else if (exposedWitnesses.nonEmpty && !abort) {
        reporter.debug(" - Unfolding the distinguishing inputs of the functions in the model")
        for (cl <- templates.witnesses.promote(exposedWitnesses)) {
          assertClause(cl)
        }
        ModelCheck
      } else if (checkModels && valid) {
        sat
      } else if (abort) {
        unknown
      } else if (checkModels && !valid) {
        if (!silentErrors) {
          reporter.error("Something went wrong. The model should have been valid, yet we got this:")
          reporter.error("  " + model.asString.replaceAll("\n", "\n  "))
          reporter.error("for formula " + andJoin(assumptionsSeq ++ constraints).asString)
        }
        unknown
      } else if (templates.quantifiers.hasAxioms) {
        val wrapped = wrapModel(umodel)
        def modelEq(e1: Encoded, e2: Encoded): Boolean =
          wrapped.modelEval(templates.mkEquals(e1, e2), t.BooleanType()) == Some(t.BooleanLiteral(true))
        val axioms = templates.quantifiers.axioms.filter { q =>
          wrapped.modelEval(q.guard, t.BooleanType()) != Some(t.BooleanLiteral(false))
        }
        val optError = axioms.view.flatMap(q => q.checkForall(modelEq).map(err => q.body -> err)).headOption

        optError match {
          // The model of a quantifier outside of the supported fragment can't be trusted from
          // the instantiations alone, but evaluating the formula can still show it holds (e.g.
          // a quantifier over an empty type, which holds vacuously). Evaluating quantifiers over
          // function calls or lambdas unfolds them, which may not terminate, so these are left out.
          case Some(_) if !axioms.exists(_.hasComplexMatchers(modelEq)) &&
              validateModel(model, assumptionsSeq, silenceErrors = true) =>
            sat
          case Some((expr, err)) =>
            if (!silentErrors) {
              reporter.error("Quantification " + expr.asString(using templates.program.printerOpts) +
                " does not fit in supported fragment.\n  Reason: " + err)
              reporter.error("Model obtained was:")
              reporter.error("  " + model.asString.replaceAll("\n", "\n  "))
            }
            unknown
          case None =>
            sat
        }
      } else {
        sat
      }
    }

    private def instantiateQuantifiers(): CheckState = {
      if (!templates.quantifiers.hasPendingInstantiations) {
        if (!silentErrors) {
          reporter.error("Something went wrong. The model is not transitive yet we can't instantiate!?")
        }
        CheckResult.cast(Unknown)
      } else {
        templates.quantifiers.promote()
        Unroll
      }
    }

    /** Checks the query without the blockers: UNSAT proves the query unsatisfiable. */
    private def proofCheck(): CheckState = {
      // The model of a proof check only serves to test whether we got lucky, to prioritize blockers
      // during unrolling and to find the congruences of calls that it breaks, so we don't request it
      // when none of these applies.
      if (ignoreModels || !(feelingLucky || modelFinding || templates.quantifiers.hasInstantiationsWithBlockers ||
          templates.congruences.hasWaiting)) {
        proofCheckWithoutModel()
      } else {
        proofCheckWithModel()
      }
    }

    private def proofCheckWithoutModel(): CheckState = {
      // check without additional model-guidance for unrolling
      reporter.debug(" - Running search without blocked literals (w/o lucky test)")

      val res = context.timers.solvers.unrolling.check.run {
          checkUnderlying(Configuration(model = false, unsatAssumptions = config.withUnsatAssumptions), refutes = true)(
            checking(ListSet.from(encodedAssumptions) ++ templates.unfolding.refutationAssumptions)
          )
        }

      reporter.debug(" - Finished search without blocked literals")

      res match {
        case Abort() =>
          CheckResult.cast(Unknown)

        case _: Unsatisfiable =>
          CheckResult.cast(res)

        case _: Satisfiable =>
          // without a model, every congruence of calls that waits for one may refute the check
          val congruences = templates.congruences.ofModel(_ => true)
          for (cl <- congruences) assertClause(cl)
          if (congruences.nonEmpty) ProofCheck else Unroll

        case otherwise => sys.error(s"Unexpected case: $otherwise")
      }
    }

    /** The model of the proof check may be a model of the query (if we are feeling lucky), and it
      * gives priority to the blockers that keep the instantiations it falsifies from being considered. */
    private def proofCheckWithModel(): CheckState = {
      if (feelingLucky) {
        reporter.debug(" - Running search without blocked literals (w/ lucky test)")
      } else {
        reporter.debug(" - Running search without blocked literals (w/o lucky test)")
      }

      // we always ask for a model here in order to give priority to blockers that
      // are keeping quantified clause instantiations from being considered
      val res: Response =
        context.timers.solvers.unrolling.check.run {
          checkUnderlying(config `max` Configuration(model = true), refutes = true)(
            checking(ListSet.from(encodedAssumptions) ++ templates.unfolding.refutationAssumptions)
          )
        }

      reporter.debug(" - Finished search without blocked literals")

      res match {
        case Abort() =>
          CheckResult.cast(Unknown)

        case _: Unsatisfiable =>
          CheckResult.cast(res)

        case SatWithModel(model) =>
          lazy val luckyModel = if (!feelingLucky) None else {
            (try { Some(withEmptyTypes(extractSimpleModel(model), model)) } catch { case _: NoSimpleValue => None })
              .filter(exModel => withinLuckyTimeout(validateModel(exModel, assumptionsSeq, silenceErrors = true)))
          }

          if (luckyModel.isDefined) {
            CheckResult(config `cast` (if (config.withModel) SatWithModel(luckyModel.get) else Sat))
          } else {
            val wrapped = wrapModel(model)

            // the congruences of the calls whose arguments the model makes equal may refute it
            val congruences = templates.congruences.ofModel(e => wrapped.eval(e, BooleanType()) == Some(BooleanLiteral(true)))
            for (cl <- congruences) assertClause(cl)

            if (congruences.nonEmpty) ProofCheck else {
              if (modelFinding) {
                for {
                  b <- templates.unfolding.satisfactionAssumptions
                  v = templates.extractNot(b).getOrElse(b)
                  if wrapped.eval(v, BooleanType()) == Some(BooleanLiteral(true))
                } templates.unfolding.promoteBlocker(v)
              }

              for {
                (inst, bs) <- templates.quantifiers.instantiationsWithBlockers
                if wrapped.eval(inst, BooleanType()) == Some(BooleanLiteral(false))
                b <- bs
              } templates.unfolding.promoteBlocker(b, force = true)

              Unroll
            }
          }
        case otherwise => sys.error(s"Unexpected case: $otherwise")
      }
    }

    private def unroll(): CheckState = {
      if (!canUnroll) {
        reporter.debug(s"- We need to keep going, but reached unroll bound ($unrollBound)")
        unrollBoundHit = true
        CheckResult.cast(Unknown)
      } else if (!templates.unfolding.canUnroll) {
        // Only satisfaction assumptions that unrolling cannot discharge are left
        reporter.debug("- We need to keep going, but nothing is left to unroll")
        CheckResult.cast(Unknown)
      } else context.timers.solvers.unrolling.unroll.run {
        reporter.debug("- We need to keep going")

        // Unrolling `unrollFactor` times
        for (i <- 1 to unrollFactor.toInt if templates.unfolding.canUnroll && !abort) {
          val newClauses = templates.unfolding.unroll
          for (ncl <- newClauses) {
            assertClause(ncl)
          }
        }

        unrollCount += 1
        if (witnessLevel > 0) witnessLevel += 1

        // the lambdas that were kept apart may be equal again, and their comparison may now decide
        for (p <- templates.witnesses.nextRound() if !abort) agreeEverywhere(p)

        reporter.debug(" - Finished unrolling")
        ModelCheck
      }
    }
  }
}

trait UnrollingSolver extends AbstractUnrollingSolver { self =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  type Encoded = t.Expr
  protected val underlying: AbstractSolver {
    val program: targetProgram.type
    type Trees = t.Expr
    type Model = targetProgram.Model
  }

  override lazy val name = "U:" + underlying.name

  override protected def certificatePrinter: Option[certificates.Certificates.Printer[Encoded]] = underlying match {
    case s: (underlying.type & certificates.Certificates.CertificatePrinter) => Some(s.certificatePrinter)
    case _ => None
  }

  // the input is printed when the program is one of the trees of the session's
  override protected def certificateInput(printer: certificates.Certificates.Printer[Encoded]):
      Option[certificates.Certificates.Encoding[Encoded]] =
    if ((program.trees: AnyRef) ne t) None
    else printer.input(program, (e: t.Expr) => encode(e.asInstanceOf[Expr])).map { input =>
      certificates.Certificates.Encoding(programEncoder.encoders, input,
        assertedConstraints.map { c =>
          val encoded = encode(c)
          (c.asInstanceOf[t.Expr], encoded, templates.simplifications.getOrElse(encoded, Seq()))
        },
        () => templates.simplifiedBodies.map { (id, steps) =>
          val fd = targetProgram.symbols.getFunction(id)
          (fd.typed(using targetProgram.symbols).applied(fd.params.map(_.toVariable)), fd.fullBody, steps)
        })
    }

  override val templates = new TemplatesImpl(targetProgram, context)

  private class TemplatesImpl(override val program: targetProgram.type, override val context: Context)
                             (using override val semantics: targetProgram.Semantics)
    extends Templates {
    import program._
    import program.trees._
    import program.symbols.{given, _}

    type Encoded = Expr

    def asString(expr: Expr): String = expr.asString
    def interrupted: Boolean = self.abort
    def interpretation(id: Identifier, tps: Seq[Type]): Option[Lambda] = self.interpretation(id, tps)

    def encodeSymbol(v: Variable): Expr = v.freshen
    def mkEncoder(bindings: Map[Variable, Expr])(e: Expr): Expr = exprOps.replaceFromSymbols(bindings, e)
    def mkSubstituter(substMap: Map[Expr, Expr]): Expr => Expr = (e: Expr) => exprOps.replace(substMap, e)

    def mkNot(e: Expr) = not(e)
    def mkOr(es: Expr*) = orJoin(es)
    def mkAnd(es: Expr*) = andJoin(es)
    def mkEquals(l: Expr, r: Expr) = Equals(l, r)
    def mkImplies(l: Expr, r: Expr) = implies(l, r)

    // declared by the SMT-LIB target (see [[smtlib.SMTLIBTarget.declareFirstOrder]])
    type Function = (Identifier, FunctionType)
    def mkFunction(name: String, from: Seq[Type], to: Type) = (FreshIdentifier(name, true), FunctionType(from, to))
    def mkFunApp(f: Function, args: Seq[Expr]) = UninterpretedCall(f._1, Seq.empty, args, f._2)

    def extractNot(e: Expr) = e match {
      case Not(e2) => Some(e2)
      case _ => None
    }

    def decodePartial(e: Expr, tpe: Type): Option[Expr] = Some(e)

    override protected def loggingRules: Boolean = self.producesProofs

    override protected def logged(kind: String, arguments: Seq[(String, Seq[Encoded])],
                                  template: Option[(TemplateContents, Map[Encoded, Encoded])], clauses: Clauses): Unit =
      self.logRule(kind, arguments, template.asInstanceOf[Option[(self.templates.TemplateContents, Map[Encoded, Encoded])]], clauses)
  }

  protected def declareVariable(v: t.Variable): t.Variable = v
  protected def wrapModel(model: targetProgram.Model): ModelWrapper = ModelWrapperImpl(model)

  private case class ModelWrapperImpl(model: targetProgram.Model) extends ModelWrapper {
    // The functions of the program call the uninterpreted functions that free functions stand for,
    // whose values the model gives
    private lazy val evalModel: targetProgram.Model = {
      val functions = templates.model.uninterpretedFunctions.toSeq.flatMap {
        case (key, (_, fT: t.Variable)) => model.vars.get(fT.toVal).map { value =>
          key -> (if (templates.model.uninterpretedConstants(key)) t.Lambda(Seq.empty, value) else value)
        }
        case _ => None
      }
      if (functions.isEmpty) model
      else inox.Model(targetProgram)(model.vars, model.interpretations ++ functions)
    }

    private def e(expr: t.Expr): Option[t.Expr] = modelEvaluator.eval(expr, evalModel).result

    def extractConstructor(elem: t.Expr, tpe: t.ADTType): Option[Identifier] = e(elem) match {
      case Some(t.ADT(id, _, _)) => Some(id)
      case _ => None
    }

    def extractSet(elem: t.Expr, tpe: t.SetType): Option[Seq[t.Expr]] = e(elem) match {
      case Some(t.FiniteSet(elems, _)) => Some(elems)
      case _ => None
    }

    def extractBag(elem: t.Expr, tpe: t.BagType): Option[Seq[(t.Expr, t.Expr)]] = e(elem) match {
      case Some(t.FiniteBag(elems, _)) => Some(elems)
      case _ => None
    }

    def extractMap(elem: t.Expr, tpe: t.MapType): Option[(Seq[(t.Expr, t.Expr)], t.Expr)] = e(elem) match {
      case Some(t.FiniteMap(elems, default, _, _)) => Some((elems, default))
      case _ => None
    }

    def modelEval(elem: t.Expr, tpe: t.Type): Option[t.Expr] = e(elem)
    def getUninterpreted(id: Identifier): Option[t.Expr] = model.interpretations.collectFirst {
      case ((cid, tps), e) if cid == id && tps.isEmpty => e
    }

    override def toString = model.asString(using targetProgram.printerOpts)
  }

  override def dbg(msg: => Any) = underlying.dbg(msg)

  override def push(): Unit = {
    super.push()
    pushUnderlying()
  }

  override def pop(): Unit = {
    super.pop()
    popUnderlying()
  }

  override def reset(): Unit = {
    resetUnderlying()
    super.reset()
  }

  override def interrupt(): Unit = {
    super.interrupt()
    underlying.interrupt()
  }

  override def free(): Unit = {
    super.free()
    underlying.free()
  }
}
