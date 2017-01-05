/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package unrolling

import utils._

import theories._
import evaluators._
import combinators._

import scala.collection.mutable.{Map => MutableMap}

object optUnrollFactor      extends IntOptionDef("unrollfactor", default = 1, "<PosInt>")
object optFeelingLucky      extends FlagOptionDef("feelinglucky", false)
object optUnrollAssumptions extends FlagOptionDef("unrollassumptions", false)
object optModelFinding      extends IntOptionDef("modelfinding", 0, "<PosInt> | 0 (off)") {
  override val parser: OptionParsers.OptionParser[Int] = (s => s match {
    case "" => Some(1)
    case _ => OptionParsers.intParser(s)
  })
}

trait AbstractUnrollingSolver extends Solver { self =>

  import program._
  import program.trees._
  import program.symbols._
  import SolverResponses._

  protected type Encoded

  protected val encoder: ast.ProgramTransformer { val sourceProgram: program.type }

  protected val theories: ast.ProgramTransformer {
    val sourceProgram: self.encoder.targetProgram.type
    val targetProgram: Program { val trees: self.encoder.targetProgram.trees.type }
  }

  protected lazy val programEncoder = encoder andThen theories

  protected lazy val s: programEncoder.sourceProgram.trees.type = programEncoder.sourceProgram.trees
  protected lazy val t: programEncoder.targetProgram.trees.type = programEncoder.targetProgram.trees
  protected lazy val targetProgram: programEncoder.targetProgram.type = programEncoder.targetProgram

  protected final def encode(vd: ValDef): t.ValDef = programEncoder.encode(vd)
  protected final def decode(vd: t.ValDef): ValDef = programEncoder.decode(vd)

  protected final def encode(v: Variable): t.Variable = programEncoder.encode(v)
  protected final def decode(v: t.Variable): Variable = programEncoder.decode(v)

  protected final def encode(e: Expr): t.Expr = programEncoder.encode(e)
  protected final def decode(e: t.Expr): Expr = programEncoder.decode(e)

  protected final def encode(tpe: Type): t.Type = programEncoder.encode(tpe)
  protected final def decode(tpe: t.Type): Type = programEncoder.decode(tpe)

  protected val templates: Templates {
    val program: targetProgram.type
    type Encoded = self.Encoded
  }

  protected val evaluator: DeterministicEvaluator with SolvingEvaluator {
    val program: self.program.type
  }

  protected val underlying: AbstractSolver {
    val program: targetProgram.type
    type Trees = Encoded
  }

  lazy val checkModels = options.findOptionOrDefault(optCheckModels)
  lazy val silentErrors = options.findOptionOrDefault(optSilentErrors)
  lazy val unrollFactor = options.findOptionOrDefault(optUnrollFactor)
  lazy val feelingLucky = options.findOptionOrDefault(optFeelingLucky)
  lazy val unrollAssumptions = options.findOptionOrDefault(optUnrollAssumptions)
  lazy val modelFinding = options.findOptionOrDefault(optModelFinding) > 0

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] =
    checkAssumptions(config)(Set.empty)

  private val constraints = new IncrementalSeq[Expr]()
  private val freeVars    = new IncrementalMap[Variable, Encoded]()

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
    abort = false
    pause = false

    templates.reset()
    constraints.reset()
    freeVars.reset()
    underlying.reset()
  }

  ctx.interruptManager.registerForInterrupts(this)

  def interrupt(): Unit = { abort = true }

  protected def declareVariable(v: t.Variable): Encoded

  def assertCnstr(expression: Expr): Unit = {
    constraints += expression
    val bindings = exprOps.variablesOf(expression).map(v => v -> freeVars.cached(v) {
      declareVariable(encode(v))
    }).toMap

    val newClauses = templates.instantiateExpr(encode(expression), bindings.map(p => encode(p._1) -> p._2))
    for (cl <- newClauses) {
      underlying.assertCnstr(cl)
    }
  }

  protected def wrapModel(model: underlying.Model): ModelWrapper

  trait ModelWrapper {
    def modelEval(elem: Encoded, tpe: t.Type): Option[t.Expr]

    def extractConstructor(elem: Encoded, tpe: t.ADTType): Option[Identifier]
    def extractSet(elem: Encoded, tpe: t.SetType): Option[Seq[Encoded]]
    def extractMap(elem: Encoded, tpe: t.MapType): Option[(Seq[(Encoded, Encoded)], Encoded)]
    def extractBag(elem: Encoded, tpe: t.BagType): Option[Seq[(Encoded, Encoded)]]

    def eval(elem: Encoded, tpe: Type): Option[Expr] = modelEval(elem, encode(tpe)).flatMap {
      expr => try {
        Some(decode(expr))
      } catch {
        case u: Unsupported => None
      }
    }

    def get(v: Variable): Option[Expr] = eval(freeVars(v), v.tpe).filter {
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

    import targetProgram._
    import targetProgram.trees._
    import targetProgram.symbols._

    // maintain extracted functions to make sure equality is well-defined
    var funExtractions: Seq[(Encoded, Lambda)] = Seq.empty

    def extractValue(v: Encoded, tpe: Type): Expr = {

      def functionsOf(v: Encoded, tpe: Type): (Seq[(Encoded, FunctionType)], Seq[Expr] => Expr) = {
        def reconstruct(subs: Seq[(Seq[(Encoded, FunctionType)], Seq[Expr] => Expr)],
                        recons: Seq[Expr] => Expr): (Seq[(Encoded, FunctionType)], Seq[Expr] => Expr) =
          (subs.flatMap(_._1), (exprs: Seq[Expr]) => {
            var curr = exprs
            recons(subs.map { case (es, recons) =>
              val (used, remaining) = curr.splitAt(es.size)
              curr = remaining
              recons(used)
            })
          })

        def rec(v: Encoded, tpe: Type): (Seq[(Encoded, FunctionType)], Seq[Expr] => Expr) = tpe match {
          case ft: FunctionType =>
            (Seq(v -> ft), es => es.head)

          case TupleType(tps) =>
            val id = Variable.fresh("tuple", tpe)
            val encoder = templates.mkEncoder(Map(id -> v)) _
            reconstruct(tps.zipWithIndex.map {
              case (tpe, index) => rec(encoder(TupleSelect(id, index + 1)), tpe)
            }, Tuple)

          case tpe @ ADTType(sid, tps) =>
            val adt = ADTType(wrapped.extractConstructor(v, tpe).get, tps)
            val id = Variable.fresh("adt", adt)
            val encoder = templates.mkEncoder(Map(id -> v)) _
            reconstruct(adt.getADT.toConstructor.fields.map {
              vd => rec(encoder(ADTSelector(id, vd.id)), vd.tpe)
            }, ADT(adt, _))

          case st @ SetType(base) =>
            val vs = wrapped.extractSet(v, st).get
            reconstruct(vs.map(rec(_, base)), FiniteSet(_, base))

          case mt @ MapType(from, to) =>
            val (vs, dflt) = wrapped.extractMap(v, mt).get
            reconstruct(vs.flatMap(p => Seq(rec(p._1, from), rec(p._2, to))) :+ rec(dflt, to), {
              case es :+ default => FiniteMap(es.grouped(2).map(s => s(0) -> s(1)).toSeq, default, from, to)
            })

          case bt @ BagType(base) =>
            val vs = wrapped.extractBag(v, bt).get
            reconstruct(vs.map(p => rec(p._1, base)), es => FiniteBag((es zip vs).map {
              case (k, (_, v)) => k -> wrapped.modelEval(v, IntegerType).get
            }, base))

          case _ => (Seq.empty, (es: Seq[Expr]) => wrapped.modelEval(v, tpe).get)
        }

        rec(v, tpe)
      }

      val ev = wrapped.modelEval(v, tpe).filterNot(_.isInstanceOf[Variable])
      if (ev.isDefined) {
        val (functions, recons) = functionsOf(v, tpe)
        recons(functions.map { case (f, tpe) =>
          extractFunction(f, bestRealType(tpe).asInstanceOf[FunctionType])
        })
      } else {
        simplestValue(tpe)
      }
    }

    object FiniteLambda {
      def apply(params: Seq[Seq[ValDef]], mappings: Seq[(Expr, Expr)], dflt: Expr): Lambda = {
        def rec(params: Seq[Seq[ValDef]], body: Expr): Expr = params match {
          case curr +: rest => rec(rest, Lambda(curr, body))
          case _ => body
        }

        val body = mappings.foldRight(dflt) { case ((cond, img), elze) => IfExpr(cond, img, elze) }
        rec(params, body).asInstanceOf[Lambda]
      }

      def extract(paramss: Seq[Seq[ValDef]], l: Lambda): (Seq[(Expr, Expr)], Expr) = (paramss, l) match {
        case (params +: rest, Lambda(args, body: Lambda)) if params == args => extract(rest, body)
        case (_, body) =>
          val params = paramss.flatten
          def rec(e: Expr): Option[(Seq[(Expr, Expr)], Expr)] = e match {
            case IfExpr(cond @ TopLevelAnds(es), thenn, elze) =>
              val indexes = es.map {
                case c @ Equals(v: Variable, _) => params.indexOf(v.toVal)
                case c @ Equals(_, v: Variable) => params.indexOf(v.toVal)
                case _ => -1
              }

              if (indexes.forall(_ >= 0) && indexes == indexes.sorted) {
                rec(elze).map { case (imgs, dflt) => ((cond -> thenn) +: imgs, dflt) }
              } else {
                None
              }
            case dflt => Some(Seq.empty, dflt)
          }

          rec(body).getOrElse((Seq.empty, body))
      }
    }

    def extractFunction(f: Encoded, tpe: FunctionType): Expr = {
      def extractLambda(f: Encoded, tpe: FunctionType): Option[Lambda] = {
        val optEqTemplate = templates.getLambdaTemplates(tpe).find { tmpl =>
          wrapped.modelEval(tmpl.start, BooleanType) == Some(BooleanLiteral(true)) &&
          wrapped.modelEval(templates.mkEquals(tmpl.ids._2, f), BooleanType) == Some(BooleanLiteral(true))
        }

        optEqTemplate.map { tmpl =>
          val localsSubst = tmpl.structure.locals.map { case (v, ev) =>
            v -> extractValue(ev, v.tpe)
          }.toMap

          val res = exprOps.replaceFromSymbols(localsSubst, tmpl.structure.body)
          val (nl, subst) = normalizeStructure(res, onlySimple = true)
          exprOps.replaceFromSymbols(subst.toMap, nl).asInstanceOf[Lambda]
        }
      }

      def extract(
        caller: Encoded,
        tpe: FunctionType,
        params: Seq[Seq[ValDef]],
        arguments: Seq[Seq[(Seq[Encoded], Expr)]],
        dflt: Expr
      ): (Lambda, Boolean) = {
        if (tpe.from.isEmpty) {
          val (result, real) = tpe.to match {
            case ft: FunctionType =>
              val nextParams = params.tail
              val nextArguments = arguments.map(_.tail)
              extract(templates.mkApp(caller, tpe, Seq.empty), ft, nextParams, nextArguments, dflt)
            case _ =>
              (extractValue(templates.mkApp(caller, tpe, Seq.empty), tpe.to), false)
          }

          (Lambda(Seq.empty, result), real)
        } else {
          extractLambda(caller, tpe).map(_ -> true).getOrElse {
            val byCondition = arguments.groupBy(_.head._2).toSeq.sortBy(p => -exprOps.formulaSize(p._1))
            val mappings = byCondition.flatMap {
              case (currCond, arguments) => tpe.to match {
                case ft: FunctionType =>
                  val (currArgs, restArgs) = (arguments.head.head._1, arguments.map(_.tail))
                  val newCaller = templates.mkApp(caller, tpe, currArgs)
                  val (res, real) = extract(newCaller, ft, params.tail, restArgs, dflt)
                  val mappings: Seq[(Expr, Expr)] = if (real) {
                    Seq(BooleanLiteral(true) -> res)
                  } else {
                    FiniteLambda.extract(params.tail, res)._1
                  }

                  mappings.map(p => (and(currCond, p._1), p._2))

                case _ =>
                  val currArgs = arguments.head.head._1
                  val res = extractValue(templates.mkApp(caller, tpe, currArgs), tpe.to)
                  Seq(currCond -> res)
              }
            }

            val lambda = FiniteLambda(params, mappings, dflt)
            // make sure `lambda` is not equal to any other distinct extracted first-class function
            val res = (funExtractions.collectFirst {
              case (encoded, `lambda`) => Right(encoded)
              case (e, img) if (
                bestRealType(img.getType) == bestRealType(lambda.getType) &&
                wrapped.modelEval(templates.mkEquals(e, f), BooleanType) == Some(BooleanLiteral(true))
              )=> Left(img)
            }) match {
              case Some(Right(enc)) => wrapped.modelEval(enc, tpe).get match {
                case Lambda(_, Let(_, Tuple(es), _)) =>
                  uniquateClosure(if (es.size % 2 == 0) -es.size / 2 else es.size / 2, lambda)
                case l => scala.sys.error("Unexpected extracted lambda format: " + l)
              }
              case Some(Left(img)) => img
              case None => lambda
            }

            funExtractions :+= f -> res

            (res, false)
          }
        }
      }

      val params: Seq[Seq[ValDef]] = {
        def rec(tpe: Type): Seq[Seq[ValDef]] = tpe match {
          case FunctionType(from, to) => from.map(tpe => ValDef(FreshIdentifier("x", true), tpe)) +: rec(to)
          case _ => Nil
        }

        rec(tpe)
      }

      val arguments = templates.getGroundInstantiations(f, tpe).flatMap { case (b, eArgs) =>
        wrapped.modelEval(b, BooleanType).filter(_ == BooleanLiteral(true)).map(_ => eArgs)
      }.distinct

      extractLambda(f, tpe).getOrElse {
        if (arguments.isEmpty) {
          wrapped.modelEval(f, tpe).get
        } else {
          val projection: Encoded = arguments.head.head

          val flatArguments: Seq[(Seq[Encoded], Seq[Option[Expr]])] =
            (for (subset <- params.flatten.toSet.subsets; args <- arguments) yield {
              val (concreteArgs, condOpts) = (params.flatten zip args).map { case (v, arg) =>
                if (!subset(v)) {
                  (arg, Some(Equals(v.toVariable, extractValue(arg, v.tpe))))
                } else {
                  (projection, None)
                }
              }.unzip

              (concreteArgs, condOpts)
            }).toSeq

          def unflatten[T](seq: Seq[T]): Seq[Seq[T]] = {
            def rec(p: Seq[Int], seq: Seq[T]): Seq[Seq[T]] = p match {
              case x +: xs => seq.take(x) +: rec(xs, seq.drop(x))
              case _ => Nil
            }

            rec(params.map(_.size), seq)
          }

          val withConds :+ ((concreteArgs, _)) = flatArguments
          val allArguments: Seq[Seq[(Seq[Encoded], Expr)]] = flatArguments.init.map {
            p => (unflatten(p._1) zip unflatten(p._2)).map(p => (p._1, andJoin(p._2.flatten)))
          }

          val (app, to) = unflatten(flatArguments.last._1).foldLeft(f -> (tpe: Type)) {
            case ((f, tpe: FunctionType), args) => (templates.mkApp(f, tpe, args), tpe.to)
          }
          val default = extractValue(app, to)

          extract(f, tpe, params, allArguments, default)._1
        }
      }
    }

    freeVars.toMap.map { case (v, idT) => v.toVal -> decode(extractValue(idT, encode(v.tpe))) }
  }

  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
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
      def unapply[A,B](resp: SolverResponse[A,B]): Boolean = resp == Unknown || abort || pause
    }

    var currentState: CheckState = ModelCheck
    while (!currentState.isInstanceOf[CheckResult]) {
      currentState = currentState match {
        case _ if abort || pause =>
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
              Validate(extractTotalModel(model))

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
          } else if (abort || pause) {
            CheckResult.cast(Unknown)
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

          // we always ask for a model here in order to give priority to blockers that
          // are keeping quantified clause instantiations from being considered
          val res: SolverResponse[underlying.Model, Set[underlying.Trees]] =
            underlying.checkAssumptions(config max Configuration(model = true))(
              encodedAssumptions.toSet ++ templates.refutationAssumptions
            )
          timer.stop()

          reporter.debug(" - Finished search without blocked literals")

          res match {
            case Abort() =>
              CheckResult.cast(Unknown)

            case _: Unsatisfiable =>
              CheckResult.cast(res)

            case SatWithModel(model) =>
              if (feelingLucky && validateModel(extractSimpleModel(model), assumptionsSeq, silenceErrors = true)) {
                if (config.withModel) CheckResult.cast(res) else CheckResult.cast(Sat)
              } else {
                val wrapped = wrapModel(model)

                if (modelFinding) {
                  for {
                    b <- templates.satisfactionAssumptions
                    v = templates.extractNot(b).getOrElse(b)
                    if wrapped.eval(v, BooleanType) == Some(BooleanLiteral(true))
                  } templates.promoteBlocker(v)
                }

                for {
                  (inst, bs) <- templates.getInstantiationsWithBlockers
                  if wrapped.eval(inst, BooleanType) == Some(BooleanLiteral(false))
                  b <- bs
                } templates.promoteBlocker(b, force = true)

                Unroll
              }
          }

        case Unroll =>
          reporter.debug("- We need to keep going")

          val timer = ctx.timers.solvers.unroll.start()
          // unfolling `unrollFactor` times
          for (i <- 1 to unrollFactor.toInt if templates.canUnroll && !abort && !pause) {
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

trait UnrollingSolver extends AbstractUnrollingSolver { self =>
  import program._
  import program.trees._
  import program.symbols._

  type Encoded = t.Expr
  val underlying: Solver {
    val program: targetProgram.type
    type Trees = t.Expr
    type Model = Map[t.ValDef, t.Expr]
  }

  override lazy val name = "U:"+underlying.name

  def free() {
    underlying.free()
  }

  object templates extends {
    val program: targetProgram.type = targetProgram
  } with Templates {
    import program._
    import program.trees._
    import program.symbols._

    type Encoded = Expr

    def asString(expr: Expr): String = expr.asString
    def abort: Boolean = self.abort
    def pause: Boolean = self.pause

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

    def extractNot(e: Expr) = e match {
      case Not(e2) => Some(e2)
      case _ => None
    }
  }

  protected val modelEvaluator: DeterministicEvaluator {
    val program: self.targetProgram.type
  }

  protected def declareVariable(v: t.Variable): t.Variable = v
  protected def wrapModel(model: Map[t.ValDef, t.Expr]): super.ModelWrapper = ModelWrapper(model)

  private case class ModelWrapper(model: Map[t.ValDef, t.Expr]) extends super.ModelWrapper {
    private def e(expr: t.Expr): Option[t.Expr] = modelEvaluator.eval(expr, model).result

    def extractConstructor(elem: t.Expr, tpe: t.ADTType): Option[Identifier] = e(elem) match {
      case Some(t.ADT(t.ADTType(id, _), _)) => Some(id)
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

    override def toString = {
      import targetProgram._
      model.map(p => p._1.asString -> p._2.asString).mkString("\n")
    }
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
}
