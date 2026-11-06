/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import theories._
import evaluators._
import combinators._

import scala.collection.mutable.{Map => MutableMap, ListBuffer}

object optUnrollBound       extends IntOptionDef("unroll-bound", default = -1, "<Int> | -1 (unbounded)")
object optUnrollFactor      extends IntOptionDef("unroll-factor", default = 1, "<PosInt>")
object optFeelingLucky      extends FlagOptionDef("feeling-lucky", false)
object optUnrollAssumptions extends FlagOptionDef("unroll-assumptions", false)

/** The semantics of equality between first-class functions.
  *
  * - [[FunctionEquality.None]]: functions can't be compared, and solvers reject queries that
  *   compare values containing functions. Counterexamples then never depend on function equality.
  * - [[FunctionEquality.Intensional]]: functions are compared structurally (Inox's historical
  *   semantics).
  * - [[FunctionEquality.Extensional]]: functions are equal iff they agree on every input.
  *
  * Under `none` and `extensional`, distinct functions always have a distinguishing input, in
  * refutations as well as in models (see [[LambdaTemplates.functionWitnesses]]). */
enum FunctionEquality {
  case None, Intensional, Extensional
}

object FunctionEquality {
  /** The comparisons between values that may contain functions in `expr`, and in the functions it
    * transitively calls, which `none` rejects. Callees are checked at the type arguments they are
    * called with, so a comparison at a type parameter counts when the parameter is instantiated with
    * a type that contains functions. The type parameters left free in `expr` are assumed not to. */
  def comparisons(program: Program)(expr: program.trees.Expr): Seq[program.trees.Expr] = {
    import program.trees._
    import program.symbols.{given, _}

    def containsFunctions(tpe: Type, seen: Set[Identifier] = Set.empty): Boolean = tpe match {
      case _: FunctionType | _: PiType => true
      case adt: ADTType =>
        !seen(adt.id) && adt.getSort.constructors.exists(_.fields.exists(vd => containsFunctions(vd.getType, seen + adt.id)))
      case NAryType(tps, _) => tps.exists(containsFunctions(_, seen))
    }

    def comparisons(e: Expr): Seq[Expr] = exprOps.collect[Expr] {
      // a constructor without functions in its fields is only equal to itself, so comparing
      // against it never compares functions
      case Equals(ADT(_, _, args), _) if !args.exists(a => containsFunctions(a.getType)) => Set.empty
      case Equals(_, ADT(_, _, args)) if !args.exists(a => containsFunctions(a.getType)) => Set.empty
      case eq @ Equals(l, _) if containsFunctions(l.getType) => Set(eq)
      case _ => Set.empty
    } (e).toSeq

    // polymorphic recursion can instantiate a function at ever larger types, so past a few
    // instantiations of the same function, we check its generic body instead
    val seen = scala.collection.mutable.Set[(Identifier, Seq[Type])]()
    val result = scala.collection.mutable.ListBuffer[Expr]()
    var queue: List[Expr] = List(expr)
    while (queue.nonEmpty) {
      val e = queue.head
      queue = queue.tail
      result ++= comparisons(e)
      for (fi <- exprOps.functionCallsOf(e)) {
        val instances = seen.count(_._1 == fi.id)
        val key = if (instances < 8) (fi.id, fi.tps) else (fi.id, getFunction(fi.id).typeArgs: Seq[Type])
        if (seen.add(key)) queue ::= getFunction(key._1, key._2).fullBody
      }
    }
    result.distinct.toSeq
  }
}

object optFunctionEquality extends OptionDef[FunctionEquality] {
  val name: String = "function-equality"
  val usageRhs: String = "none|intensional|extensional"
  val default: FunctionEquality = FunctionEquality.Intensional
  override def formatDefault: String = default.toString.toLowerCase

  override def parser: OptionParsers.OptionParser[FunctionEquality] = s =>
    FunctionEquality.values.find(_.toString.toLowerCase == s.toLowerCase)
}
object optModelFinding      extends IntOptionDef("model-finding", 0, "<PosInt> | 0 (off)") {
  override val parser: OptionParsers.OptionParser[Int] = (s => s match {
    case "" => Some(1)
    case _ => OptionParsers.intParser(s)
  })
}

object AbstractUnrollingSolver {

  private def computeProgramEncoder(prog: Program,
                                    enc: transformers.ProgramTransformer {val sourceProgram: prog.type},
                                    chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type},
                                    theoriesCtor: transformers.ProgramTransformer {
                                      val sourceProgram: prog.type
                                      val targetProgram: chooses.targetProgram.type
                                    } => transformers.ProgramTransformer {
                                      val sourceProgram: chooses.targetProgram.type
                                      val targetProgram: Program {val trees: enc.targetProgram.trees.type}
                                    }):
  (transformers.ProgramTransformer {
    val sourceProgram: prog.type
    val targetProgram: Program {val trees: enc.targetProgram.trees.type}
  }) = {
    val fullEncoder = enc `andThen` chooses
    val theories = theoriesCtor(fullEncoder)
    fullEncoder `andThen` theories
  }
}

abstract class AbstractUnrollingSolver private
  (override val program: Program,
   override val context: Context)
  // Alias for `program`, as there are some places where `program` is shadowed.
  (val prog: program.type)
  (val enc: transformers.ProgramTransformer {val sourceProgram: program.type})
  (val chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type})
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
                   chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type},
                   programEncoder: transformers.ProgramTransformer {
                     val sourceProgram: prog.type
                     val targetProgram: Program {val trees: enc.targetProgram.trees.type}
                   })
                  (using semantics: prog.Semantics,
                   semanticsProvider: SemanticsProvider {val trees: enc.targetProgram.trees.type}) =
    this(prog, context)(prog)(enc)(chooses)(programEncoder)(using semantics, programEncoder.targetProgram.getSemantics(using semanticsProvider))

  def this(prog: Program,
           context: Context,
           enc: transformers.ProgramTransformer {val sourceProgram: prog.type},
           chooses: ChooseEncoder {val program: prog.type; val sourceEncoder: enc.type})
          // Given a `fullEncoder` (constructed by `enc andThen chooses`), produce a theory
          (theoriesCtor: transformers.ProgramTransformer {
            val sourceProgram: prog.type
            val targetProgram: chooses.targetProgram.type
          } => transformers.ProgramTransformer {
            val sourceProgram: chooses.targetProgram.type
            val targetProgram: Program {val trees: enc.targetProgram.trees.type}
          })
          (using semantics: prog.Semantics,
           semanticsProvider: SemanticsProvider {val trees: enc.targetProgram.trees.type}) =
    this(prog, context, enc, chooses, AbstractUnrollingSolver.computeProgramEncoder(prog, enc, chooses, theoriesCtor))

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
  lazy val unrollAssumptions = options.findOptionOrDefault(optUnrollAssumptions)
  lazy val modelFinding = options.findOptionOrDefault(optModelFinding) > 0

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    checkAssumptions(config)(Set.empty)

  protected val freeVars  = new IncrementalMap[Variable, Encoded]()
  private val constraints = new IncrementalSeq[Expr]()
  private val freeChooses = new IncrementalMap[Choose, Encoded]()

  /** The equality literals of the on-demand distinguishing inputs that the last model extraction
    * needed (see [[LambdaTemplates.onDemandWitnesses]]). */
  private var requestedWitnesses: Map[Encoded, Int] = Map.empty

  /** The on-demand distinguishing inputs of the functions that show up in the last extracted model,
    * which then join the regular unfolding (see [[LambdaTemplates.promoteWitnesses]]). */
  private var exposedWitnesses: Set[Encoded] = Set.empty

  protected var failures: ListBuffer[Throwable] = new ListBuffer
  protected var abort: Boolean = false
  protected var pause: Boolean = false

  def push(): Unit = {
    templates.push()
    constraints.push()
    freeVars.push()
  }

  def pop(): Unit = {
    templates.pop()
    constraints.pop()
    freeVars.pop()
  }

  def reset() = {
    failures.clear()
    abort = false
    pause = false

    templates.reset()
    constraints.reset()
    freeVars.reset()
    underlying.reset()
  }

  def interrupt(): Unit = { abort = true }

  def free(): Unit = context.interruptManager.unregisterForInterrupts(this)

  protected def declareVariable(v: t.Variable): Encoded

  private def removeChooses(expr: Expr): (Expr, Map[Variable, Encoded]) = {
    var chooseBindings: Map[Variable, Encoded] = Map.empty
    val withoutChooses = exprOps.postMap {
      case c: Choose =>
        val v = c.res.toVariable
        chooseBindings += v -> freeChooses.cached(c)(declareVariable(encode(v)))
        Some(Assume(c.pred, v))
      case _ => None
    } (expr)

    (withoutChooses, chooseBindings)
  }

  def declare(vd: ValDef): Unit = context.timers.solvers.declare.run(try {
    context.timers.solvers.declare.sanity.run {
      assert(vd.getType.isTyped)
    }

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

    val freeBindings: Map[Variable, Encoded] = (typeOps.variablesOf(vd.tpe) + vd.toVariable).map {
      v => v -> freeVars.cached(v)(declareVariable(encode(v)))
    }.toMap

    val newClauses = context.timers.solvers.declare.clauses.run {
      templates.instantiateVariable(encode(vd.toVariable), freeBindings.map(p => encode(p._1) -> p._2))
    }

    context.timers.solvers.declare.underlying.run {
      for (cl <- newClauses) {
        underlying.assertCnstr(cl)
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
  }

  def assertCnstr(expression: Expr): Unit = context.timers.solvers.assert.run(try {
    context.timers.solvers.assert.sanity.run {
      symbols.ensureWellFormed // make sure that the current program is well-formed
      typeCheck(expression, BooleanType()) // make sure we've asserted a boolean-typed expression
      if (functionEquality == FunctionEquality.None) checkNoFunctionComparisons(expression)
    }

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

    constraints += expression

    val (withoutChooses, chooseBindings) = removeChooses(expression)

    val freeBindings: Map[Variable, Encoded] = exprOps.variablesOf(withoutChooses).map {
      v => v -> freeVars.cached(v)(declareVariable(encode(v)))
    }.toMap

    val newClauses = context.timers.solvers.assert.clauses.run {
      templates.instantiateExpr(
        encode(withoutChooses),
        (freeBindings ++ chooseBindings).map(p => encode(p._1) -> p._2)
      )
    }

    context.timers.solvers.assert.underlying.run {
      for (cl <- newClauses) {
        underlying.assertCnstr(cl)
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

    def getChoose(id: Identifier): Option[t.Expr]

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
      val vs = extracted.map { case (v, e) => v.toVal -> exprOps.replaceFromSymbols(extracted, e) }

      val cs = templates.getCalls
        .filter(p => modelEval(p._1, t.BooleanType()) == Some(t.BooleanLiteral(true)))
        .map(_._2)
        .groupBy(_.tfd)
        .flatMap { case (tfd, calls) =>
          chooses.getChoose(tfd.fd).map { case (id, c, vds) =>
            val tpSubst = tfd.tpSubst.map(p => decode(p._1).asInstanceOf[TypeParameter] -> decode(p._2))
            val from = tfd.params.map(_.getType(using tfd.symbols))
            val to = tfd.getType
            import templates._

            val inst = new typeOps.TypeInstantiator(tpSubst)
            val tvds = vds map inst.transform
            val tc = inst.transform(c.copy(res = c.res.freshen))

            val mappings = calls.flatMap { call =>
              val optArgs = (call.args zip from).map(p => modelEval(p._1.encoded, p._2))
              val optRes = modelEval(mkCall(tfd, call.args.map(_.encoded)), to)
              if (optArgs.forall(_.isDefined) && optRes.isDefined) {
                Some(optArgs.map(_.get) -> optRes.get)
              } else {
                None
              }
            }

            val body = mappings.foldRight(tc: Expr) { case ((args, img), elze) =>
              IfExpr(andJoin((tvds zip args).map { case (vd, arg) =>
                Equals(vd.toVariable, decode(arg))
              }), decode(img), elze)
            }

            (id, tfd.tps.map(decode(_))) -> body
          }
        }

      val freeCs = freeChooses.toMap.map { case (c, idT) =>
        (c.res.id, Seq.empty[Type]) -> extract(idT, c.res.getType)
      }

      def choosesOf(e: Expr, tps: Seq[Type]): Map[(Identifier, Seq[Type]), Expr] = exprOps.collect {
        case c: Choose => getChoose(c.res.id).map(e => (c.res.id, tps) -> decode(e)).toSet
        case _ => Set.empty[((Identifier, Seq[Type]), Expr)]
      } (e).toMap

      val modelCs = vs.values.toSeq.flatMap(e => choosesOf(e, Seq.empty)) ++
        (cs ++ freeCs).flatMap { case ((id, tps), e) => choosesOf(e, tps) }

      inox.Model(program)(vs, cs ++ freeCs ++ modelCs)
    }
  }

  // Model values are compared as the solver sees them: functions are equal iff they are the same
  // function value, which the encoding makes structural (see [[optFunctionEquality]]).
  protected lazy val modelEvaluator: DeterministicEvaluator { val program: self.targetProgram.type } =
    targetSemantics.getEvaluator(using context.withOpts(
      optIgnoreContracts(true), optFunctionEquality(FunctionEquality.Intensional)))

  private def emit(silenceErrors: Boolean)(msg: String) =
    if (silenceErrors) reporter.debug(msg) else reporter.warning(msg)

  private def validateModel(model: program.Model, assumptions: Seq[Expr], silenceErrors: Boolean): Boolean = {
    val expr = andJoin(assumptions ++ constraints)

    val typingCond = andJoin(model.vars.toSeq.map { case (v, value) =>
      def rec(e: Expr, tpe: Type): Expr = (e, tpe) match {
        // The models of functions are conditionals over their arguments, and their default values
        // are chosen in their codomains (see `defaultValue`)
        case (Let(vd, value, body), tpe) => Let(vd, value, rec(body, tpe)).copiedFrom(body)
        case (IfExpr(cond, thenn, elze), tpe) => IfExpr(cond, rec(thenn, tpe), rec(elze, tpe)).copiedFrom(e)
        case (c: Choose, _) if c.res.tpe != c.res.getType => BooleanLiteral(true)
        case (ADT(id, _, args), adt @ ADTType(_, tps)) =>
          andJoin((args zip getConstructor(id, tps).fields).map(p => rec(p._1, p._2.tpe)))
        case (Tuple(es), TupleType(tps)) =>
          andJoin((es zip tps).map(p => rec(p._1, p._2)))
        case (FiniteSet(elems, _), SetType(base)) =>
          andJoin(elems.map(e => rec(e, base)))
        case (FiniteBag(elems, _), BagType(base)) =>
          andJoin(elems.map(p => and(rec(p._1, base), rec(p._2, IntegerType()))))
        case (FiniteMap(elems, dflt, _, _), MapType(from, to)) =>
          andJoin(elems.map(p => and(rec(p._1, from), rec(p._2, to))) :+ rec(dflt, to))
        case (Lambda(params, body), FunctionType(from, to)) =>
          val nparams = (params zip from).map { case (vd, tpe) => vd.copy(tpe = tpe) }
          forall(nparams, rec(
            exprOps.replaceFromSymbols((params zip nparams.map(_.toVariable)).toMap, body), to))
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
        case (c: Choose, tpe) =>
          BooleanLiteral(
            c.res.tpe == tpe && tpe == tpe.getType && // choose is for a simple type
            (model.chooses contains (c.res.id -> Seq())) // the model contains a mapping for the choose
          )
        case _ => BooleanLiteral(true)
      }

      rec(value, v.tpe)
    })

    // we have to check case class constructors in model for ADT invariants
    val newExpr = model.vars.toSeq.foldRight(and(typingCond, expr)) {
      case ((v, value), e) => Let(v, value, e)
    }

    val evaluator = semantics.getEvaluator(using context.withOpts(
      optSilentErrors(silenceErrors),
      optCheckModels(checkModels || feelingLucky)
    ))

    evaluator.eval(newExpr, inox.Model(program)(Map.empty, model.chooses)) match {
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
    var chooseExtractions: Seq[(Encoded, Choose)] = Seq.empty

    // evaluating in the model can be costly, and extraction compares the same functions repeatedly
    val modelEqualities = MutableMap.empty[(Encoded, Encoded), Boolean]
    def modelEq(e1: Encoded, e2: Encoded): Boolean = e1 == e2 || modelEqualities.getOrElseUpdate(e1 -> e2,
      wrapped.modelEval(templates.mkEquals(e1, e2), BooleanType()) == Some(BooleanLiteral(true)))

    lazy val onDemandWitnesses = templates.onDemandWitnesses.groupMap(_._1)(_._2)
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
        encode(program.symbols.simplestValue(decode(tpe.getType)))
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
      case RefinementType(vd, pred) => and(refinementsOf(e, vd.tpe), exprOps.replaceFromSymbols(Map(vd -> e), pred))
      case TupleType(tps) => andJoin(tps.zipWithIndex.map((tpe, i) => refinementsOf(TupleSelect(e, i + 1), tpe)))
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
      case _ => tpe
    }

    /* The default value of the model of a function, i.e. its value on the arguments the formula
     * doesn't apply it to. It must lie in the codomain `to` (in terms of `params`) for all arguments
     * in the domain, so a refined codomain is chosen as `choose(r: {r: to | domain ==> r in to})`.
     * Function-typed parameters can't be checked by an expression, so they're assumed in the domain. */
    def defaultValue(params: Seq[ValDef], paramTypes: Seq[Type], to: Type): Option[Expr] =
      Option.when(to != to.getType) {
        val domain = andJoin((params zip paramTypes).collect {
          case (vd, tpe) if isFirstOrder(tpe) => refinementsOf(vd.toVariable, tpe)
        })
        Choose(ValDef.fresh("res", guardedType(domain, to), true), BooleanLiteral(true))
      }

    def extractFunction(f: Encoded, fullType: Type, seen: Map[FunctionType, Set[Encoded]]): Expr = {
      val tpe = fullType.getType.asInstanceOf[FunctionType]
      val nextSeen = seen + (tpe -> (seen(tpe) + f))
      extractedFunctions += tpe -> (extractedFunctions.getOrElse(tpe, Set.empty) + f)

      def extractLambda(f: Encoded, tpe: FunctionType): Option[Lambda] = {
        val optEqTemplate = templates.getLambdaTemplates(tpe).find { tmpl =>
          wrapped.modelEval(tmpl.start, BooleanType()) == Some(BooleanLiteral(true)) &&
          modelEq(tmpl.ids._2, f)
        }

        optEqTemplate.map { tmpl =>
          val localsSubst = tmpl.structure.locals.map { case (v, ev) =>
            v -> extractValue(ev, v.getType, nextSeen)
          }.toMap

          val res = exprOps.replaceFromSymbols(localsSubst, tmpl.structure.body)
          val (nl, subst) = normalizeStructure(res, onlySimple = true)
          exprOps.replaceFromSymbols(subst.map { case (v, e, _) => v -> e }.toMap, nl).asInstanceOf[Lambda]
        }
      }

      val params: Seq[ValDef] = tpe.from.map(tpe => ValDef.fresh("x", tpe, true))

      // The parameter and result types of `fullType` in terms of `params`
      val (paramTypes, resultType) = fullType match {
        case PiType(ps, to) =>
          val subst: Map[ValDef, Expr] = (ps zip params.map(_.toVariable)).toMap
          (ps.map(vd => typeOps.replaceFromSymbols(subst, vd.tpe)), typeOps.replaceFromSymbols(subst, to))
        case FunctionType(from, to) => (from, to)
        case _ => (tpe.from, tpe.to)
      }

      // Results are extracted with their full types when these don't depend on the arguments
      val imageType = if ((typeOps.variablesOf(resultType) & params.map(_.toVariable).toSet).isEmpty) resultType
        else resultType.getType

      // Applications to distinguishing inputs come last, so that they don't determine the default
      // value of the extracted function (which must agree with quantifier instantiations).
      val arguments = templates.getGroundInstantiations(f, tpe).flatMap { case (b, eArgs) =>
        wrapped.modelEval(b, BooleanType()).filter(_ == BooleanLiteral(true)).map(_ => eArgs)
      }.distinct.sortBy(_.exists(templates.isWitnessArgument))

      extractLambda(f, tpe).orElse {
        if (seen(tpe).exists(e => modelEq(f, e))) {
          Some(chooseExtractions.collectFirst { case (e, c) if modelEq(f, e) => c }.getOrElse {
            val c = Choose(Variable.fresh("x", tpe, true).toVal, BooleanLiteral(true))
            chooseExtractions :+= f -> c
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
          Lambda(Seq.empty, extractValue(templates.mkApp(f, tpe, Seq.empty), imageType, nextSeen))
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
                val inputs = templates.distinguishingInputs.collectFirst {
                  case ((f1, f2), (tpe, ws)) if tpe == ft &&
                    ((modelEq(f1, a) && modelEq(f2, b)) || (modelEq(f1, b) && modelEq(f2, a))) &&
                    !modelEq(templates.mkApp(a, ft, ws), templates.mkApp(b, ft, ws)) => ws
                }

                // the pair may only have an on-demand distinguishing input, which we then request
                if (inputs.isEmpty) {
                  for ((tpe, ws) <- onDemandWitnesses if tpe == ft; (f1, f2, equality, depth) <- ws
                       if (modelEq(f1, a) && modelEq(f2, b)) || (modelEq(f1, b) && modelEq(f2, a))) {
                    requestedWitnesses += equality -> depth
                  }
                }

                inputs.flatMap { ws =>
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
                    (Seq.empty, extractValue(templates.mkApp(f, tpe, concreteArgs), resType, nextSeen))
                }
            }
            case None =>
              val withConds :+ ((concreteArgs, _, _)) = argumentsWithConds: @unchecked
              (withConds, extractValue(templates.mkApp(f, tpe, concreteArgs), imageType, nextSeen))
          }

          // arguments whose conditions are trivial are covered by the default value
          val sortedArguments = withConds
            .filter(_._2 != BooleanLiteral(true))
            .groupBy(_._2)
            .view.mapValues(_.head)
            .toSeq
            .sortBy(p => -exprOps.formulaSize(p._1))

          val mappings = sortedArguments.map { case (cond, (arguments, _, resType)) =>
            (cond, extractValue(templates.mkApp(f, tpe, arguments), resType, nextSeen))
          }

          val lambda = Lambda(params, mappings.foldRight(default) {
            case ((cond, img), elze) => IfExpr(cond, img, elze)
          })

          // make sure `lambda` is not equal to any other distinct extracted first-class function
          (lambdaExtractions.collectFirst {
            case (e, img) if img.getType == lambda.getType && modelEq(e, f) => Left(img)
            case (encoded, `lambda`) => Right(encoded)
          }) match {
            case Some(Right(enc)) => wrapped.modelEval(enc, tpe).getOrThrow match {
              case Lambda(_, Let(_, Tuple(es), _)) =>
                uniquateClosure(if (es.size % 2 == 0) -es.size / 2 else es.size / 2, lambda)
              case l => throw new InternalSolverError(name, "Unexpected extracted lambda format: " + l.asString)
            }
            case Some(Left(img)) => img
            case None => lambda
          }
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
    val exChooses = chooseExtractions.toMap.map { case (e, c) =>
      c -> lambdaExtractions.collectFirst {
        case (f, lambda) if lambda.getType == c.res.getType && modelEq(f, e) => lambda
      }.get
    }
    val chooses = exChooses.map(p => (p._1.res.id, Seq.empty[s.Type]) -> decodeOrSimplest(p._2))

    // The distinct functions of the model need a distinguishing input, so on-demand pairs join the
    // regular unfolding once they show up in it (see [[LambdaTemplates.onDemandWitnesses]]): a free
    // function with the other free functions of the model, and with the lambdas that the model
    // instantiates. Pairs of lambdas are left to the extraction of the functions they are passed to
    // (see `argumentCondition`). We don't ask the model whether the functions are distinct, as solvers
    // may evaluate the equality of function values extensionally: their unfolding is guarded by it.
    for {
      (tpe, ws) <- onDemandWitnesses
      fs <- extractedFunctions.get(tpe).toSeq
      lambdas = templates.getLambdaTemplates(tpe).map(tmpl => tmpl.ids._2 -> tmpl.start).toMap
      (f1, f2, equality, _) <- ws
      if !lambdas.contains(f1) && fs.exists(modelEq(_, f1)) && (lambdas.get(f2) match {
        case Some(start) => wrapped.modelEval(start, BooleanType()) == Some(BooleanLiteral(true))
        case None => fs.exists(modelEq(_, f2))
      })
    } exposedWitnesses += equality

    inox.Model(program)(exModel.vars, exModel.chooses ++ chooses)
  }

  protected val emptyModel: Model =
    inox.Model(program)(Map.empty, Map.empty)

  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] =
      context.timers.solvers.unrolling.run(scala.util.Try({

    // throw error immediately if a previous call has already failed
    if (failures.nonEmpty) throw failures.head

    // Multiple calls to registerForInterrupts are (almost) idempotent and acceptable
    context.interruptManager.registerForInterrupts(this)

    val assumptionsSeq       : Seq[Expr]          = assumptions.toSeq
    val encodedAssumptions   : Seq[Encoded]       = assumptionsSeq.map { expr =>
      val vars = exprOps.variablesOf(expr)
      templates.mkEncoder(vars.map(v => encode(v) -> freeVars(v)).toMap)(encode(expr))
    }
    val encodedToAssumptions : Map[Encoded, Expr] = (encodedAssumptions zip assumptionsSeq).toMap

    def decodeAssumptions(core: Set[Encoded]): Set[Expr] = {
      core.flatMap(ast => encodedToAssumptions.get(ast) match {
        case Some(n @ Not(_: Variable)) => Some(n)
        case Some(v: Variable) => Some(v)
        case _ => None
      })
    }

    import SolverResponses._

    sealed abstract class CheckState
    class CheckResult(val response: config.Response[Model, Assumptions]) extends CheckState
    case class Validate(model: underlying.Model) extends CheckState
    case object ModelCheck extends CheckState
    case object FiniteRangeCheck extends CheckState
    case object InstantiateQuantifiers extends CheckState
    case object ProofCheck extends CheckState
    case object Unroll extends CheckState

    object CheckResult {
      def cast(resp: SolverResponse[underlying.Model, Set[underlying.Trees]]): CheckResult = {
        // unsat assumptions may have been requested internally (eg. for witness assumptions)
        val res = resp match {
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
        if (failures.nonEmpty || abort || pause) {
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

    var unrollCount: Int = 0

    def canUnroll: Boolean = unrollBound < 0 || unrollCount < unrollBound

    // The depth up to which distinguishing inputs are instantiated: 0 until the first model is found,
    // then one more level with each unrolling (see [[LambdaTemplates.witnessEqualities]])
    var witnessLevel: Int = 0
    def witnessEqualities: Map[Encoded, Int] =
      if (witnessLevel > 0) templates.witnessEqualities else Map.empty

    /* The equalities between functions without distinguishing inputs that appear in the unsat core
     * of `res`, or all of them if the solver gave no core. Cores aren't necessarily reported as
     * literals, so they are compared modulo negation. */
    def coreEqualities(
      res: SolverResponse[underlying.Model, Set[underlying.Trees]],
      equalities: Map[Encoded, Int]
    ): Map[Encoded, Int] = res match {
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
    def instantiateWitnesses(needed: Map[Encoded, Int]): CheckState = {
      val current = needed.filter(_._2 <= witnessLevel).keySet
      if (current.nonEmpty) {
        reporter.debug(" - Instantiating distinguishing function inputs")
        for (cl <- templates.instantiateWitnesses(current)) {
          underlying.assertCnstr(cl)
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
    def blamedEqualities(
      inCore: Map[Encoded, Int],
      equalities: Map[Encoded, Int],
      withoutEqualities: => SolverResponse[underlying.Model, Set[underlying.Trees]]
    ): Either[CheckState, SolverResponse[underlying.Model, Set[underlying.Trees]]] = {
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

    var currentState: CheckState = ModelCheck
    while (!currentState.isInstanceOf[CheckResult]) {
      currentState = currentState match {
        case ModelCheck =>
          reporter.debug(" - Running search...")

          val equalities = witnessEqualities
          val getModel = !templates.requiresFiniteRangeCheck || checkModels || templates.hasAxioms || config.withModel
          val getAssumptions = (unrollAssumptions && templates.canUnroll) || config.withUnsatAssumptions ||
            equalities.nonEmpty
          val checkConfig = Configuration(model = getModel && !ignoreModels, unsatAssumptions = getAssumptions)

          def check(equalities: Iterable[Encoded]): SolverResponse[underlying.Model, Set[underlying.Trees]] =
            context.timers.solvers.unrolling.check.run {
              underlying.checkAssumptions(checkConfig)(
                encodedAssumptions.toSet ++ templates.satisfactionAssumptions ++ equalities
              )
            }

          val resWithEqualities = check(equalities.keys)

          reporter.debug(" - Finished search with blocked literals")

          // the equalities are only assumed in `resWithEqualities`, so that every UNSAT answer below
          // comes from a check without them
          val next: Either[CheckState, SolverResponse[underlying.Model, Set[underlying.Trees]]] = resWithEqualities match {
            case Abort() => Right(resWithEqualities)
            case _: Unsatisfiable if equalities.nonEmpty =>
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
              case _: Satisfiable if witnessLevel == 0 && templates.witnessEqualities.nonEmpty =>
                witnessLevel = 1
                ModelCheck

              case _: Satisfiable if templates.requiresFiniteRangeCheck =>
                FiniteRangeCheck

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
              case _: Unsatisfiable if !templates.canUnroll && templates.satisfactionAssumptions.isEmpty =>
                CheckResult.cast(res)

              case UnsatWithAssumptions(assumptions) if unrollAssumptions =>
                for (b <- assumptions) templates.promoteBlocker(b)
                ProofCheck

              case _ =>
                ProofCheck
            }
          }

        case FiniteRangeCheck =>
          reporter.debug(" - Verifying finite ranges")

          val clauses = templates.getFiniteRangeClauses

          // the model must have distinguishing inputs as well (see [[ModelCheck]])
          val equalities = witnessEqualities

          val next: Either[CheckState, SolverResponse[underlying.Model, Set[underlying.Trees]]] =
            context.timers.solvers.unrolling.check.run {
              underlying.push()
              for (cl <- encodedAssumptions.toSeq ++ templates.satisfactionAssumptions ++ clauses) {
                underlying.assertCnstr(cl)
              }
              def check(equalities: Iterable[Encoded]) =
                underlying.checkAssumptions(Configuration(model = true, unsatAssumptions = equalities.nonEmpty))(
                  equalities.toSet
                )
              val res = check(equalities.keys)
              val next = res match {
                case _: Unsatisfiable if equalities.nonEmpty && !abort && !pause =>
                  val inCore = coreEqualities(res, equalities).filter(_._2 <= witnessLevel)
                  if (inCore.nonEmpty) Left(inCore)
                  else check(Seq.empty) match {
                    case _: Satisfiable => Left(equalities.filter(_._2 <= witnessLevel))
                    case _ => Right(res)
                  }
                case _ => Right(res)
              }
              underlying.pop()
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

        case Validate(umodel) =>
          requestedWitnesses = Map.empty
          exposedWitnesses = Set.empty
          val validated = (try { Some(extractTotalModel(umodel)) } catch {
            case NoSimpleValue(tpe) =>
              if (!silentErrors) {
                reporter.error("No simple value found for type " + tpe.asString)
              }
              None
            case Canceled() => None
          }).map[CheckState] { model =>
            lazy val sat = CheckResult(config `cast` (if (config.withModel) SatWithModel(model) else Sat))
            lazy val unknown = CheckResult `cast` Unknown

            lazy val valid = !checkModels || validateModel(model, assumptionsSeq, silenceErrors = silentErrors)

            // the extracted functions need these distinguishing inputs to tell their arguments apart,
            // and they are unfolded fairly, like the others (see [[LambdaTemplates.witnessEqualities]])
            val requested = requestedWitnesses.filter(_._2 <= (witnessLevel max 1)).keySet
            if (requested.nonEmpty && !abort && !pause) {
              reporter.debug(" - Instantiating requested distinguishing function inputs")
              for (cl <- templates.instantiateWitnesses(requested)) {
                underlying.assertCnstr(cl)
              }
              ModelCheck
            } else if (requestedWitnesses.nonEmpty && functionEquality == FunctionEquality.None && !abort && !pause) {
              // Without function equality, the model can't compare the functions instead, so we wait
              // for the unfolding to reach their distinguishing inputs (see [[instantiateWitnesses]]).
              reporter.debug(" - Requested distinguishing function inputs are deeper than the unfolding")
              witnessLevel = witnessLevel max 1
              ProofCheck
            } else if (exposedWitnesses.nonEmpty && !abort && !pause) {
              reporter.debug(" - Unfolding the distinguishing inputs of the functions in the model")
              for (cl <- templates.promoteWitnesses(exposedWitnesses)) {
                underlying.assertCnstr(cl)
              }
              ModelCheck
            } else if (checkModels && valid) {
              sat
            } else if (abort || pause) {
              unknown
            } else if (checkModels && !valid) {
              if (!silentErrors) {
                reporter.error("Something went wrong. The model should have been valid, yet we got this:")
                reporter.error("  " + model.asString.replaceAll("\n", "\n  "))
                reporter.error("for formula " + andJoin(assumptionsSeq ++ constraints).asString)
              }
              unknown
            } else if (templates.hasAxioms) {
              val wrapped = wrapModel(umodel)
              val optError = templates.getAxioms.view.flatMap { q =>
                if (wrapped.modelEval(q.guard, t.BooleanType()) != Some(t.BooleanLiteral(false))) {
                  q.checkForall { (e1, e2) =>
                    wrapped.modelEval(templates.mkEquals(e1, e2), t.BooleanType()) == Some(t.BooleanLiteral(true))
                  }.map(err => q.body -> err)
                } else {
                  None
                }
              }.headOption

              optError match {
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
          }.getOrElse(CheckResult `cast` Unknown)

          validated

        case InstantiateQuantifiers =>
          if (templates.quantificationsManager.unrollGeneration.isEmpty) {
            if (!silentErrors) {
              reporter.error("Something went wrong. The model is not transitive yet we can't instantiate!?")
            }
            CheckResult.cast(Unknown)
          } else {
            templates.promoteQuantifications
            Unroll
          }

        case ProofCheck if ignoreModels =>
          // check without additional model-guidance for unrolling
          reporter.debug(" - Running search without blocked literals (w/o lucky test)")

          val res = context.timers.solvers.unrolling.check.run {
              underlying.checkAssumptions(Configuration(model = false, unsatAssumptions = config.withUnsatAssumptions))(
                encodedAssumptions.toSet ++ templates.refutationAssumptions
              )
            }

          reporter.debug(" - Finished search without blocked literals")

          res match {
            case Abort() =>
              CheckResult.cast(Unknown)

            case _: Unsatisfiable =>
              CheckResult.cast(res)

            case _: Satisfiable =>
              Unroll

            case otherwise => sys.error(s"Unexpected case: $otherwise")
          }

        case ProofCheck =>
          if (feelingLucky) {
            reporter.debug(" - Running search without blocked literals (w/ lucky test)")
          } else {
            reporter.debug(" - Running search without blocked literals (w/o lucky test)")
          }

          // we always ask for a model here in order to give priority to blockers that
          // are keeping quantified clause instantiations from being considered
          val res: SolverResponse[underlying.Model, Set[underlying.Trees]] =
            context.timers.solvers.unrolling.check.run {
              underlying.checkAssumptions(config `max` Configuration(model = true))(
                encodedAssumptions.toSet ++ templates.refutationAssumptions
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
                (try { Some(extractSimpleModel(model)) } catch { case _: NoSimpleValue => None })
                  .filter(exModel => validateModel(exModel, assumptionsSeq, silenceErrors = true))
              }

              if (luckyModel.isDefined) {
                CheckResult(config `cast` (if (config.withModel) SatWithModel(luckyModel.get) else Sat))
              } else {
                val wrapped = wrapModel(model)

                if (modelFinding) {
                  for {
                    b <- templates.satisfactionAssumptions
                    v = templates.extractNot(b).getOrElse(b)
                    if wrapped.eval(v, BooleanType()) == Some(BooleanLiteral(true))
                  } templates.promoteBlocker(v)
                }

                for {
                  (inst, bs) <- templates.getInstantiationsWithBlockers
                  if wrapped.eval(inst, BooleanType()) == Some(BooleanLiteral(false))
                  b <- bs
                } templates.promoteBlocker(b, force = true)

                Unroll
              }
            case otherwise => sys.error(s"Unexpected case: $otherwise")
          }

        case Unroll if !canUnroll =>
          reporter.debug(s"- We need to keep going, but reached unroll bound ($unrollBound)")
          CheckResult.cast(Unknown)

        case Unroll if !templates.canUnroll =>
          // Only satisfaction assumptions that unrolling cannot discharge are left,
          // e.g. a model exists only if some type parameter is empty.
          reporter.debug("- We need to keep going, but nothing is left to unroll")
          CheckResult.cast(Unknown)

        case Unroll => context.timers.solvers.unrolling.unroll.run {
          reporter.debug("- We need to keep going")

          // Unrolling `unrollFactor` times
          for (i <- 1 to unrollFactor.toInt if templates.canUnroll && !abort && !pause) {
            val newClauses = templates.unroll
            for (ncl <- newClauses) {
              underlying.assertCnstr(ncl)
            }
          }

          unrollCount += 1
          if (witnessLevel > 0) witnessLevel += 1

          reporter.debug(" - Finished unrolling")
          ModelCheck
        }

        case otherwise => sys.error(s"Unexpected case: $otherwise")
      }
    }

    val CheckResult(res) = currentState: @unchecked
    res
  }).recover {
    case e @ (_: InternalSolverError | _: Unsupported) =>
      if (reporter.isDebugEnabled) reporter.debug(e)
      else if (!silentErrors && !abort) reporter.error(e.getMessage)
      config.cast(Unknown)
  }.get)
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

  override val templates = new TemplatesImpl(targetProgram, context)

  private class TemplatesImpl(override val program: targetProgram.type, override val context: Context)
                             (using override val semantics: targetProgram.Semantics)
    extends Templates {
    import program._
    import program.trees._
    import program.symbols.{given, _}

    type Encoded = Expr

    def asString(expr: Expr): String = expr.asString
    def abort: Boolean = self.abort
    def pause: Boolean = self.pause

    def encodeSymbol(v: Variable): Expr = v.freshen
    def mkEncoder(bindings: Map[Variable, Expr])(e: Expr): Expr = exprOps.replaceFromSymbols(bindings, e)
    def mkSubstituter(substMap: Map[Expr, Expr]): Expr => Expr = (e: Expr) => exprOps.replace(substMap, e)

    def mkNot(e: Expr) = not(e)
    def mkOr(es: Expr*) = orJoin(es)
    def mkAnd(es: Expr*) = andJoin(es)
    def mkEquals(l: Expr, r: Expr) = Equals(l, r)
    def mkImplies(l: Expr, r: Expr) = implies(l, r)

    def extractNot(e: Expr) = e match {
      case Not(e2) => Some(e2)
      case _ => None
    }

    def decodePartial(e: Expr, tpe: Type): Option[Expr] = Some(e)
  }

  protected def declareVariable(v: t.Variable): t.Variable = v
  protected def wrapModel(model: targetProgram.Model): ModelWrapper = ModelWrapperImpl(model)

  private case class ModelWrapperImpl(model: targetProgram.Model) extends ModelWrapper {
    private def e(expr: t.Expr): Option[t.Expr] = modelEvaluator.eval(expr, model).result

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
    def getChoose(id: Identifier): Option[t.Expr] = model.chooses.collectFirst {
      case ((cid, tps), e) if cid == id && tps.isEmpty => e
    }

    override def toString = model.asString(using targetProgram.printerOpts)
  }

  override def dbg(msg: => Any) = underlying.dbg(msg)

  override def push(): Unit = {
    super.push()
    underlying.push()
  }

  override def pop(): Unit = {
    super.pop()
    underlying.pop()
  }

  override def reset(): Unit = {
    underlying.reset()
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
