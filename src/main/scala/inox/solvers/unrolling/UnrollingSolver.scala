/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import theories._
import evaluators._

object optUnrollFactor extends InoxLongOptionDef("unrollfactor",  "Number of unfoldings to perform in each unfold step", default = 1, "<PosInt>")
object optFeelingLucky extends InoxFlagOptionDef("feelinglucky",  "Use evaluator to find counter-examples early", false)
object optUnrollCores  extends InoxFlagOptionDef("unrollcores",   "Use unsat-cores to drive unfolding while remaining fair", false)
object optAssumePre    extends InoxFlagOptionDef("assumepre",     "Assume precondition holds (pre && f(x) = body) when unfolding", false)

trait AbstractUnrollingSolver
  extends Solver {

  import program._
  import program.trees._
  import program.symbols._

  val theories: TheoryEncoder
  lazy val encodedProgram: Program { val trees: program.trees.type } = theories.encode(program)

  type Encoded
  implicit val printable: Encoded => Printable

  val templates: Templates {
    val program: encodedProgram.type
    type Encoded = AbstractUnrollingSolver.this.Encoded
  }

  val evaluator: DeterministicEvaluator with SolvingEvaluator {
    val program: AbstractUnrollingSolver.this.program.type
  }

  val unfoldFactor     = options.findOptionOrDefault(optUnrollFactor)
  val feelingLucky     = options.findOptionOrDefault(optFeelingLucky)
  val checkModels      = options.findOptionOrDefault(optCheckModels)
  val unrollUnsatCores = options.findOptionOrDefault(optUnrollCores)
  val assumePreHolds   = options.findOptionOrDefault(optAssumePre)
  val silentErrors     = options.findOptionOrDefault(optSilentErrors)

  def check(model: Boolean = false, cores: Boolean = false): SolverResponses.SolverResponse =
    checkAssumptions(model = model, cores = cores)(Set.empty)

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
      solverAssert(cl)
    }
  }

  def solverAssert(cnstr: Encoded): Unit

  /** Simpler version of [[Solver.SolverResponses]] used internally in
    * [[AbstractUnrollingSolver]] and children.
    *
    * These enable optimizations for the native Z3 solver (such as avoiding
    * full Z3 model extraction in certain cases).
    */
  protected sealed trait Response
  protected case object Unknown extends Response
  protected case class Unsat(cores: Option[Set[Encoded]]) extends Response
  protected case class Sat(model: Option[ModelWrapper]) extends Response

  /** Provides CPS solver.check call. CPS is necessary in order for calls that
   *  depend on solver.getModel to be able to access the model BEFORE the call
   *  to solver.pop() is issued.
   *
   *  The underlying solver therefore performs the following sequence of
   *  solver calls:
   *  {{{
   *    solver.push()
   *    for (cls <- clauses) solver.assertCnstr(cls)
   *    val res = solver.check
   *    block(res)
   *    solver.pop()
   *  }}}
   *
   *  This ordering guarantees that [[block]] can safely call solver.getModel.
   *
   *  This sequence of calls can also be used to mimic solver.checkAssumptions()
   *  for solvers that don't support the construct natively.
   */
  def solverCheck[R](clauses: Seq[Encoded], model: Boolean = false, cores: Boolean = false)
                    (block: Response => R): R

  /** We define solverCheckAssumptions in CPS in order for solvers that don't
   *  support this feature to be able to use the provided [[solverCheck]] CPS
   *  construction.
   */
  def solverCheckAssumptions[R](assumptions: Seq[Encoded], model: Boolean = false, cores: Boolean = false)
                               (block: Response => R): R = solverCheck(assumptions)(block)

  trait ModelWrapper {
    def modelEval(elem: Encoded, tpe: Type): Option[Expr]

    def eval(elem: Encoded, tpe: Type): Option[Expr] = modelEval(elem, theories.encode(tpe)).flatMap {
      expr => try {
        Some(theories.decode(expr)(Map.empty))
      } catch {
        case u: Unsupported => None
      }
    }

    def get(v: Variable): Option[Expr] = eval(freeVars(v), theories.encode(id.getType)).filter {
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

  private def extractSimpleModel(wrapper: ModelWrapper): Map[ValDef, Expr] = {
    freeVars.toMap.map { case (v, _) => v.toVal -> wrapper.get(v).getOrElse(simplestValue(v.getType)) }
  }

  private def extractTotalModel(wrapper: ModelWrapper): Map[ValDef, Expr] = {
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

        case CaseClass(cct, es) => reconstruct((cct.tcd.toCase.fields zip es).map {
          case (vd, e) => rec(e, CaseClassSelector(selector, vd.id))
        }, CaseClass(cct, _))

        case _ => (Seq.empty, (es: Seq[Expr]) => expr)
      }

      rec(expr, selector)
    }

    import templates.{QuantificationTypeMatcher => QTM}
    freeVars.toMap.map { case (v, idT) =>
      val value = wrapper.get(v).getOrElse(simplestValue(v.getType))
      val (functions, recons) = functionsOf(value, v)

      v.toVal -> recons(functions.map { case (f, selector) =>
        val encoded = templates.mkEncoder(Map(v -> idT))(selector)
        val tpe = bestRealType(f.getType).asInstanceOf[FunctionType]
        val QTM(from, to) = tpe

        if (from.isEmpty) f else {
          val params = from.map(tpe => Variable(FreshIdentifier("x", true), tpe))
          val app = templates.mkApplication(selector, params)

          val allImages = templates.getGroundInstantiations(encoded, tpe).flatMap { case (b, eArgs) =>
            wrapper.eval(b, BooleanType).filter(_ == BooleanLiteral(true)).flatMap { _ =>
              val optArgs = (eArgs zip from).map { case (arg, tpe) => wrapper.eval(arg, tpe) }
              val eApp = templates.mkEncoder(Map(v -> idT) ++ (params zip eArgs))(app)
              val optResult = wrapper.eval(eApp, to)

              if (optArgs.forall(_.isDefined) && optResult.isDefined) {
                val args = optArgs.map(_.get)
                val result = optResult.get
                Some(args -> result)
              } else {
                None
              }
            }
          }

          val default = if (allImages.isEmpty) {
            def rec(e: Expr): Expr = e match {
              case Lambda(_, body) => rec(body)
              case IfExpr(_, _, elze) => rec(elze)
              case e => e
            }

            rec(f)
          } else {
            val optDefault = allImages.collectFirst {
              case (firstArg +: otherArgs, result) if otherArgs.forall { o =>
                evaluator.eval(Equals(firstArg, o)).result == Some(BooleanLiteral(true))
              } => result
            }

            optDefault.getOrElse {
              val app = templates.mkApplication(f, Seq.fill(from.size)(allImages.head._1.head))
              evaluator.eval(app).result.getOrElse {
                scala.sys.error("Unexpectedly failed to evaluate " + app.asString)
              }
            }
          }

          val body = allImages.foldRight(default) { case ((args, result), elze) =>
            IfExpr(andJoin((params zip args).map(p => Equals(p._1, p._2))), result, elze)
          }

          def mkLambda(params: Seq[ValDef], body: Expr): Lambda = body.getType match {
            case FunctionType(from, to) =>
              val (rest, curr) = params.splitAt(params.size - from.size)
              mkLambda(rest, Lambda(curr, body))
            case _ => Lambda(params, body)
          }

          mkLambda(params.map(_.toVal), body)
        }
      })
    }
  }

  def checkAssumptions(model: Boolean = false, cores: Boolean = false)(assumptions: Set[Expr]) = {

    val assumptionsSeq       : Seq[Expr]          = assumptions.toSeq
    val encodedAssumptions   : Seq[Encoded]       = assumptionsSeq.map { expr =>
      val vars = exprOps.variablesOf(expr)
      templates.mkEncoder(vars.map(v => theories.encode(v) -> freeVars(v)).toMap)(expr)
    }
    val encodedToAssumptions : Map[Encoded, Expr] = (encodedAssumptions zip assumptionsSeq).toMap

    def encodedCoreToCore(core: Set[Encoded]): Set[Expr] = {
      core.flatMap(ast => encodedToAssumptions.get(ast) match {
        case Some(n @ Not(_: Variable)) => Some(n)
        case Some(v: Variable) => Some(v)
        case _ => None
      })
    }

    sealed abstract class CheckState
    class CheckResult(val response: SolverResponses.SolverResponse) extends CheckState
    case class Validate(model: Option[Map[ValDef, Expr]]) extends CheckState
    case object ModelCheck extends CheckState
    case object FiniteRangeCheck extends CheckState
    case object InstantiateQuantifiers extends CheckState
    case object ProofCheck extends CheckState
    case object Unroll extends CheckState

    object CheckResult {
      def apply(resp: SolverResponses.SolverResponse) = new CheckResult(resp)
      def apply(resp: Response): CheckResult = new CheckResult(resp match {
        case Unknown           => SolverResponses.Unknown
        case Sat(None)         => SolverResponses.SatResponse
        case Sat(Some(model))  => SolverResponses.SatResponseWithModel(extractSimpleModel(model))
        case Unsat(None)       => SolverResponses.UnsatResponse
        case Unsat(Some(core)) => SolverResponses.UnsatResponseWithCores(encodedCoreToCore(core))
      })
      def unapply(res: CheckResult): Option[SolverResponses.SolverResponse] = Some(res.response)
    }

    object Abort {
      def unapply(resp: Response): Boolean = resp == Unknown || interrupted
    }

    var currentState: CheckState = ModelCheck
    while (!currentState.isInstanceOf[CheckResult]) {
      currentState = currentState match {
        case _ if interrupted =>
          CheckResult(Unknown)

        case ModelCheck =>
          reporter.debug(" - Running search...")

          val withModel = model && !templates.requiresFiniteRangeCheck
          val withCores = cores || unrollUnsatCores

          val timer = ctx.timers.solvers.check.start()
          solverCheckAssumptions(
            encodedAssumptions.toSeq ++ templates.satisfactionAssumptions,
            model = withModel,
            cores = withCores
          ) { res =>
            timer.stop()

            reporter.debug(" - Finished search with blocked literals")

            res match {
              case Abort() =>
                CheckResult(Unknown)

              case sat: Sat =>
                if (templates.requiresFiniteRangeCheck) {
                  FiniteRangeCheck
                } else {
                  Validate(sat.model.map(extractSimpleModel))
                }

              case _: Unsat if !templates.canUnroll =>
                CheckResult(res)

              case Unsat(Some(cores)) if unrollUnsatCores =>
                for (c <- cores) templates.extractNot(c) match {
                  case Some(b) => templates.promoteBlocker(b)
                  case None => reporter.fatalError("Unexpected blocker polarity for unsat core unrolling: " + c)
                }
                ProofCheck

              case _ => 
                ProofCheck
            }
          }

        case FiniteRangeCheck =>
          reporter.debug(" - Verifying finite ranges")

          val clauses = templates.getFiniteRangeClauses
          val timer = ctx.timers.solvers.check.start()
          solverCheck(
            encodedAssumptions.toSeq ++ templates.satisfactionAssumptions ++ clauses,
            model = model
          ) { res =>
            timer.stop()

            reporter.debug(" - Finished checking finite ranges")

            res match {
              case Abort() =>
                CheckResult(Unknown)

              case Sat(optModel) =>
                Validate(optModel.map(extractTotalModel))

              case _ =>
                InstantiateQuantifiers
            }
          }

        case Validate(optModel) => optModel match {
          case None => CheckResult(SolverResponses.SatResponse)
          case Some(model) =>
            val valid = !checkModels || validateModel(model, assumptionsSeq, silenceErrors = silentErrors)
            if (valid) {
              CheckResult(SolverResponses.SatResponseWithModel(model))
            } else {
              reporter.error(
                "Something went wrong. The model should have been valid, yet we got this: " +
                model.toString +
                " for formula " + andJoin(assumptionsSeq ++ constraints).asString)
              CheckResult(Unknown)
            }
        }

        case InstantiateQuantifiers =>
          if (!templates.quantificationsManager.unrollGeneration.isDefined) {
            reporter.error("Something went wrong. The model is not transitive yet we can't instantiate!?")
            CheckResult(Unknown)
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
          solverCheckAssumptions(
            encodedAssumptions.toSeq ++ templates.refutationAssumptions,
            model = feelingLucky,
            cores = cores
          ) { res =>
            timer.stop()

            reporter.debug(" - Finished search without blocked literals")

            res match {
              case Abort() =>
                CheckResult(Unknown)

              case _: Unsat =>
                CheckResult(res)

              case Sat(Some(model)) if feelingLucky =>
                if (validateModel(extractSimpleModel(model), assumptionsSeq, silenceErrors = true)) {
                  CheckResult(res)
                } else {
                  for {
                    (inst, bs) <- templates.getInstantiationsWithBlockers
                    if model.eval(inst, BooleanType) == Some(BooleanLiteral(false))
                    b <- bs
                  } templates.promoteBlocker(b, force = true)

                  Unroll
                }

              case _ =>
                Unroll
            }
          }

        case Unroll =>
          reporter.debug("- We need to keep going")

          val timer = ctx.timers.solvers.unroll.start()
          // unfolling `unfoldFactor` times
          for (i <- 1 to unfoldFactor.toInt) {
            val newClauses = templates.unroll
            for (ncl <- newClauses) {
              solverAssert(ncl)
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
  val solver: Solver { val program: encodedProgram.type }

  override val name = "U:"+solver.name

  def free() {
    solver.free()
  }

  val printable = (e: Expr) => e

  val templates = new Templates {
    val program = encodedProgram
    type Encoded = Expr

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

    def extractNot(e: Expr): Option[Expr] = e match {
      case Not(b) => Some(b)
      case _ => None
    }
  }

  def declareVariable(v: Variable): Variable = v

  def solverAssert(cnstr: Expr): Unit = {
    solver.assertCnstr(cnstr)
  }

  case class Model(model: Map[ValDef, Expr]) extends ModelWrapper {
    def modelEval(elem: Expr, tpe: Type): Option[Expr] = evaluator.eval(elem, model).result
    override def toString = model.mkString("\n")
  }

  def solverCheck[R](clauses: Seq[Expr], model: Boolean = false, cores: Boolean = false)(block: Response => R): R = {
    solver.push()
    for (cls <- clauses) solver.assertCnstr(cls)
    val res = solver.check(model = model, cores = cores) match {
      case solver.SolverResponses.Unknown                       => Unknown
      case solver.SolverResponses.UnsatResponse                 => Unsat(None)
      case solver.SolverResponses.UnsatResponseWithCores(cores) => Unsat(Some(cores))
      case solver.SolverResponses.SatResponse                   => Sat(None)
      case solver.SolverResponses.SatResponseWithModel(model)   => Sat(Some(Model(model)))
    }
    val r = block(res)
    solver.pop()
    r
  }

  override def dbg(msg: => Any) = solver.dbg(msg)

  override def push(): Unit = {
    super.push()
    solver.push()
  }

  override def pop(): Unit = {
    super.pop()
    solver.pop()
  }

  override def reset(): Unit = {
    solver.reset()
    super.reset()
  }

  override def interrupt(): Unit = {
    super.interrupt()
    solver.interrupt()
  }

  override def recoverInterrupt(): Unit = {
    solver.recoverInterrupt()
    super.recoverInterrupt()
  }
}
