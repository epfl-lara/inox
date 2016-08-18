/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import theories._
import evaluators._

object optUnrollFactor extends InoxLongOptionDef(
  "unrollfactor",      "Number of unfoldings to perform in each unfold step", default = 1, "<PosInt>")

object optFeelingLucky extends InoxFlagOptionDef(
  "feelinglucky",      "Use evaluator to find counter-examples early", false)

object optUnrollAssumptions  extends InoxFlagOptionDef(
  "unrollassumptions", "Use unsat-assumptions to drive unfolding while remaining fair", false)

trait AbstractUnrollingSolver
  extends Solver {

  import program._
  import program.trees._
  import program.symbols._

  import SolverResponses._

  protected type Encoded

  protected val theories: TheoryEncoder { val sourceProgram: program.type }

  protected val templates: Templates {
    val program: theories.targetProgram.type
    type Encoded = AbstractUnrollingSolver.this.Encoded
  }

  protected val evaluator: DeterministicEvaluator with SolvingEvaluator {
    val program: AbstractUnrollingSolver.this.program.type
  }

  protected val underlying: AbstractSolver {
    val program: AbstractUnrollingSolver.this.theories.targetProgram.type
    type Trees = Encoded
  }

  lazy val checkModels = options.findOptionOrDefault(optCheckModels)
  lazy val silentErrors = options.findOptionOrDefault(optSilentErrors)
  lazy val unrollFactor = options.findOptionOrDefault(optUnrollFactor)
  lazy val feelingLucky = options.findOptionOrDefault(optFeelingLucky)
  lazy val unrollAssumptions = options.findOptionOrDefault(optUnrollAssumptions)

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    checkAssumptions(config)(Set.empty)

  private val constraints = new IncrementalSeq[Expr]()
  private val freeVars    = new IncrementalMap[Variable, Encoded]()

  protected var interrupted : Boolean = false

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

  override def reset() = {
    interrupted = false

    templates.reset()
    constraints.reset()
    freeVars.reset()
  }

  override def interrupt(): Unit = {
    interrupted = true
  }

  override def recoverInterrupt(): Unit = {
    interrupted = false
  }

  protected def declareVariable(v: Variable): Encoded

  def assertCnstr(expression: Expr): Unit = {
    constraints += expression
    val bindings = exprOps.variablesOf(expression).map(v => v -> freeVars.cached(v) {
      declareVariable(theories.encode(v))
    }).toMap

    val newClauses = templates.instantiateExpr(expression, bindings)
    for (cl <- newClauses) {
      underlying.assertCnstr(cl)
    }
  }

  protected def wrapModel(model: underlying.Model): ModelWrapper

  trait ModelWrapper {
    protected def modelEval(elem: Encoded, tpe: Type): Option[Expr]

    def eval(elem: Encoded, tpe: Type): Option[Expr] = modelEval(elem, theories.encode(tpe)).flatMap {
      expr => try {
        Some(theories.decode(expr))
      } catch {
        case u: Unsupported => None
      }
    }

    def get(v: Variable): Option[Expr] = eval(freeVars(v), v.getType).filter {
      case v: Variable => false
      case _ => true
    }
  }

  private def emit(silenceErrors: Boolean)(msg: String) =
    if (silenceErrors) reporter.debug(msg) else reporter.warning(msg)

  private def validateModel(model: Map[ValDef, Expr], assumptions: Seq[Expr], silenceErrors: Boolean): Boolean = {
    val expr = andJoin(assumptions ++ constraints)

    // we have to check case class constructors in model for ADT invariants
    val newExpr = model.toSeq.foldLeft(expr) { case (e, (v, value)) => let(v, value, e) }

    evaluator.eval(newExpr) match {
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

  private def extractSimpleModel(model: underlying.Model): Map[ValDef, Expr] = {
    val wrapped = wrapModel(model)
    freeVars.toMap.map { case (v, _) => v.toVal -> wrapped.get(v).getOrElse(simplestValue(v.getType)) }
  }

  private def extractTotalModel(model: underlying.Model): Map[ValDef, Expr] = {
    val wrapped = wrapModel(model)
    def functionsOf(expr: Expr, selector: Expr): (Seq[(Expr, Expr)], Seq[Expr] => Expr) = {
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

      def rec(expr: Expr, selector: Expr): (Seq[(Expr, Expr)], Seq[Expr] => Expr) = expr match {
        case (_: Lambda) =>
          (Seq(expr -> selector), (es: Seq[Expr]) => es.head)

        case Tuple(es) => reconstruct(es.zipWithIndex.map {
          case (e, i) => rec(e, TupleSelect(selector, i + 1))
        }, Tuple)

        case ADT(adt, es) => reconstruct((adt.getADT.toConstructor.fields zip es).map {
          case (vd, e) => rec(e, ADTSelector(selector, vd.id))
        }, ADT(adt, _))

        case _ => (Seq.empty, (es: Seq[Expr]) => expr)
      }

      rec(expr, selector)
    }

    import templates.{QuantificationTypeMatcher => QTM}
    freeVars.toMap.map { case (v, idT) =>
      val value = wrapped.get(v).getOrElse(simplestValue(v.getType))
      val (functions, recons) = functionsOf(value, v)

      v.toVal -> recons(functions.map { case (f, selector) =>
        val encoded = templates.mkEncoder(Map(v -> idT))(selector)
        val tpe = bestRealType(f.getType).asInstanceOf[FunctionType]
        val QTM(from, to) = tpe

        if (from.isEmpty) f else {
          val params = from.map(tpe => Variable(FreshIdentifier("x", true), tpe))
          val app = templates.mkApplication(selector, params)

          val allImages = templates.getGroundInstantiations(encoded, tpe).flatMap { case (b, eArgs) =>
            wrapped.eval(b, BooleanType).filter(_ == BooleanLiteral(true)).flatMap { _ =>
              val optArgs = (eArgs zip from).map { case (arg, tpe) => wrapped.eval(arg, tpe) }
              val eApp = templates.mkEncoder(Map(v -> idT) ++ (params zip eArgs))(app)
              val optResult = wrapped.eval(eApp, to)

              if (optArgs.forall(_.isDefined) && optResult.isDefined) {
                val args = optArgs.map(_.get)
                val result = optResult.get
                Some(args -> result)
              } else {
                None
              }
            }
          }.distinct

          def mkLambda(params: Seq[ValDef], body: Expr): Lambda = body.getType match {
            case FunctionType(from, to) =>
              val (rest, curr) = params.splitAt(params.size - from.size)
              mkLambda(rest, Lambda(curr, body))
            case _ => Lambda(params, body)
          }

          if (allImages.isEmpty) {
            def rec(e: Expr): Expr = e match {
              case Lambda(_, body) => rec(body)
              case IfExpr(_, _, elze) => rec(elze)
              case e => e
            }

            mkLambda(params.map(_.toVal), rec(f))
          } else {
            val projection: Expr = allImages.head._1.head

            val allResults: Seq[(Seq[Expr], Expr)] =
              (for (subset <- params.toSet.subsets; (args, _) <- allImages) yield {
                val (concreteArgs, condOpts) = (params zip args).map { case (v, arg) =>
                  if (!subset(v)) {
                    (arg, Some(Equals(v, arg)))
                  } else {
                    (projection, None)
                  }
                }.unzip

                val app = templates.mkApplication(f, concreteArgs)
                val result = evaluator.eval(app).result.getOrElse {
                  scala.sys.error("Unexpectedly failed to evaluate " + app.asString)
                }

                condOpts.flatten -> result
              }).toSeq

            val withConds :+ ((Seq(), default)) = allResults
            val body = withConds.foldRight(default) { case ((conds, result), elze) =>
              IfExpr(andJoin(conds), result, elze)
            }

            mkLambda(params.map(_.toVal), body)
          }
        }
      })
    }
  }

  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
    val assumptionsSeq       : Seq[Expr]          = assumptions.toSeq
    val encodedAssumptions   : Seq[Encoded]       = assumptionsSeq.map { expr =>
      val vars = exprOps.variablesOf(expr)
      templates.mkEncoder(vars.map(v => theories.encode(v) -> freeVars(v)).toMap)(expr)
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
    case class Validate(model: Map[ValDef, Expr]) extends CheckState
    case object ModelCheck extends CheckState
    case object FiniteRangeCheck extends CheckState
    case object InstantiateQuantifiers extends CheckState
    case object ProofCheck extends CheckState
    case object Unroll extends CheckState

    object CheckResult {
      def cast(resp: SolverResponse[underlying.Model, Set[underlying.Trees]]): CheckResult =
        new CheckResult(config.convert(config.cast(resp), extractSimpleModel, decodeAssumptions))

      def apply[M <: Model, A <: Assumptions](resp: config.Response[M, A]) = new CheckResult(resp)
      def unapply(res: CheckResult): Option[config.Response[Model, Assumptions]] = Some(res.response)
    }

    object Abort {
      def unapply[A,B](resp: SolverResponse[A,B]): Boolean = resp == Unknown || interrupted
    }

    var currentState: CheckState = ModelCheck
    while (!currentState.isInstanceOf[CheckResult]) {
      currentState = currentState match {
        case _ if interrupted =>
          CheckResult.cast(Unknown)

        case ModelCheck =>
          reporter.debug(" - Running search...")

          val checkConfig = config
            .min(Configuration(model = !templates.requiresFiniteRangeCheck, unsatAssumptions = true))
            .max(Configuration(model = false, unsatAssumptions = unrollAssumptions && templates.canUnroll))

          val timer = ctx.timers.solvers.check.start()
          val res: SolverResponse[underlying.Model, Set[underlying.Trees]] =
            underlying.checkAssumptions(checkConfig)(
              encodedAssumptions.toSet ++ templates.satisfactionAssumptions
            )
          timer.stop()

          reporter.debug(" - Finished search with blocked literals")

          res match {
            case Abort() =>
              CheckResult.cast(Unknown)

            case Sat if templates.requiresFiniteRangeCheck =>
              FiniteRangeCheck

            case Sat =>
              CheckResult.cast(Sat)

            case SatWithModel(model) =>
              Validate(extractSimpleModel(model))

            case _: Unsatisfiable if !templates.canUnroll =>
              CheckResult.cast(res)

            case UnsatWithAssumptions(assumptions) if unrollAssumptions =>
              for (b <- assumptions) templates.promoteBlocker(b)
              ProofCheck

            case _ => 
              ProofCheck
          }

        case FiniteRangeCheck =>
          reporter.debug(" - Verifying finite ranges")

          val clauses = templates.getFiniteRangeClauses

          val timer = ctx.timers.solvers.check.start()
          underlying.push()
          for (cl <- encodedAssumptions.toSeq ++ templates.satisfactionAssumptions ++ clauses) {
            underlying.assertCnstr(cl)
          }
          val res: SolverResponse[underlying.Model, Set[underlying.Trees]] = underlying.check(Model min config)
          underlying.pop()
          timer.stop()

          reporter.debug(" - Finished checking finite ranges")

          res match {
            case Abort() =>
              CheckResult.cast(Unknown)

            case Sat =>
              CheckResult.cast(Sat)

            case SatWithModel(model) =>
              Validate(extractTotalModel(model))

            case _ =>
              InstantiateQuantifiers
          }

        case Validate(model) =>
          val valid: Boolean = !checkModels ||
            validateModel(model, assumptionsSeq, silenceErrors = silentErrors)

          if (valid) {
            CheckResult(config cast SatWithModel(model))
          } else {
            reporter.error(
              "Something went wrong. The model should have been valid, yet we got this: " +
              model.toString +
              " for formula " + andJoin(assumptionsSeq ++ constraints).asString)
            CheckResult.cast(Unknown)
          }

        case InstantiateQuantifiers =>
          if (templates.quantificationsManager.unrollGeneration.isEmpty) {
            reporter.error("Something went wrong. The model is not transitive yet we can't instantiate!?")
            CheckResult.cast(Unknown)
          } else {
            templates.promoteQuantifications
            Unroll
          }

        case ProofCheck =>
          if (feelingLucky) {
            reporter.debug(" - Running search without blocked literals (w/ lucky test)")
          } else {
            reporter.debug(" - Running search without blocked literals (w/o lucky test)")
          }

          val timer = ctx.timers.solvers.check.start()
          val res: SolverResponse[underlying.Model, Set[underlying.Trees]] =
            underlying.checkAssumptions(config max Configuration(model = feelingLucky))(
              encodedAssumptions.toSet ++ templates.refutationAssumptions
            )
          timer.stop()

          reporter.debug(" - Finished search without blocked literals")

          res match {
            case Abort() =>
              CheckResult.cast(Unknown)

            case _: Unsatisfiable =>
              CheckResult.cast(res)

            case SatWithModel(model) if feelingLucky =>
              if (validateModel(extractSimpleModel(model), assumptionsSeq, silenceErrors = true)) {
                CheckResult.cast(res)
              } else {
                val wrapped = wrapModel(model)
                for {
                  (inst, bs) <- templates.getInstantiationsWithBlockers
                  if wrapped.eval(inst, BooleanType) == Some(BooleanLiteral(false))
                  b <- bs
                } templates.promoteBlocker(b, force = true)

                Unroll
              }

            case _ =>
              Unroll
          }

        case Unroll =>
          reporter.debug("- We need to keep going")

          val timer = ctx.timers.solvers.unroll.start()
          // unfolling `unrollFactor` times
          for (i <- 1 to unrollFactor.toInt) {
            val newClauses = templates.unroll
            for (ncl <- newClauses) {
              underlying.assertCnstr(ncl)
            }
          }
          timer.stop()

          reporter.debug(" - finished unrolling")
          ModelCheck
      }
    }

    val CheckResult(res) = currentState
    res
  }
}

trait UnrollingSolver extends AbstractUnrollingSolver {
  import program._
  import program.trees._
  import program.symbols._

  type Encoded = Expr
  val underlying: Solver {
    val program: theories.targetProgram.type
    type Trees = Expr
    type Model = Map[ValDef, Expr]
  }

  override val name = "U:"+underlying.name

  def free() {
    underlying.free()
  }

  object templates extends {
    val program: theories.targetProgram.type = theories.targetProgram
  } with Templates {
    type Encoded = Expr

    def asString(expr: Expr): String = expr.asString

    def encodeSymbol(v: Variable): Expr = v.freshen
    def mkEncoder(bindings: Map[Variable, Expr])(e: Expr): Expr =
      exprOps.replaceFromSymbols(bindings, e)
    def mkSubstituter(substMap: Map[Expr, Expr]): Expr => Expr =
      (e: Expr) => exprOps.replace(substMap, e)

    def mkNot(e: Expr) = not(e)
    def mkOr(es: Expr*) = orJoin(es)
    def mkAnd(es: Expr*) = andJoin(es)
    def mkEquals(l: Expr, r: Expr) = Equals(l, r)
    def mkImplies(l: Expr, r: Expr) = implies(l, r)
  }

  protected def declareVariable(v: Variable): Variable = v
  protected def wrapModel(model: Map[ValDef, Expr]): super.ModelWrapper = ModelWrapper(model)

  private case class ModelWrapper(model: Map[ValDef, Expr]) extends super.ModelWrapper {
    def modelEval(elem: Expr, tpe: Type): Option[Expr] = evaluator.eval(elem, model).result
    override def toString = model.mkString("\n")
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

  override def recoverInterrupt(): Unit = {
    underlying.recoverInterrupt()
    super.recoverInterrupt()
  }
}
