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
    val fullEncoder = enc andThen chooses
    val theories = theoriesCtor(fullEncoder)
    fullEncoder andThen theories
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

  def assertCnstr(expression: Expr): Unit = context.timers.solvers.assert.run(try {
    context.timers.solvers.assert.sanity.run {
      symbols.ensureWellFormed // make sure that the current program is well-formed
      typeCheck(expression, BooleanType()) // make sure we've asserted a boolean-typed expression
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
      val vs = freeVars.toMap.map { case (v, idT) => v.toVal -> extract(idT, v.getType) }

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

  private def emit(silenceErrors: Boolean)(msg: String) =
    if (silenceErrors) reporter.debug(msg) else reporter.warning(msg)

  private def validateModel(model: program.Model, assumptions: Seq[Expr], silenceErrors: Boolean): Boolean = {
    val expr = andJoin(assumptions ++ constraints)

    val typingCond = andJoin(model.vars.toSeq.map { case (v, value) =>
      def rec(e: Expr, tpe: Type): Expr = (e, tpe) match {
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
    wrapped.getModel((e, tpe) => wrapped.eval(e, tpe).getOrElse(simplestValue(tpe)))
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

    def modelEq(e1: Encoded, e2: Encoded): Boolean =
      wrapped.modelEval(templates.mkEquals(e1, e2), BooleanType()) == Some(BooleanLiteral(true))

    def extractValue(v: Encoded, tpe: Type, seen: Map[FunctionType, Set[Encoded]]): Expr = {

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
            }, Tuple.apply)

          case tpe @ ADTType(sid, tps) =>
            val cons = wrapped.extractConstructor(v, tpe).getOrThrow
            val id = Variable.fresh("adt", tpe)
            val encoder = templates.mkEncoder(Map(id -> v)) _
            reconstruct(getConstructor(cons, tps).fields.map {
              vd => rec(encoder(ADTSelector(id, vd.id)), vd.getType)
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

      val ev = wrapped.modelEval(v, tpe).filterNot(_.isInstanceOf[Variable])
      if (ev.isDefined) {
        val (functions, recons) = functionsOf(v, tpe)
        recons(functions.map { case (f, tpe) =>
          extractFunction(f, tpe, seen)
        })
      } else {
        encode(program.symbols.simplestValue(decode(tpe)))
      }
    }

    def extractFunction(f: Encoded, tpe: FunctionType, seen: Map[FunctionType, Set[Encoded]]): Expr = {
      val nextSeen = seen + (tpe -> (seen(tpe) + f))

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
      val arguments = templates.getGroundInstantiations(f, tpe).flatMap { case (b, eArgs) =>
        wrapped.modelEval(b, BooleanType()).filter(_ == BooleanLiteral(true)).map(_ => eArgs)
      }.distinct

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
          wrapped.modelEval(f, tpe).getOrThrow.asInstanceOf[Lambda]
        } else if (tpe.from.isEmpty) {
          Lambda(Seq.empty, extractValue(templates.mkApp(f, tpe, Seq.empty), tpe.to, nextSeen))
        } else {
          val projections: Map[Type, Encoded] = (arguments.head zip params)
            .groupBy(p => p._2.getType)
            .view.mapValues(_.head._1).toMap

          val exArguments = for (args <- arguments) yield {
            (params zip args).map { case (vd, arg) => extractValue(arg, vd.getType, nextSeen) }
          }

          val argumentsWithConds: Seq[(Seq[Encoded], Expr)] =
            (for (subset <- params.toSet.subsets(); (args, exArgs) <- arguments zip exArguments) yield {
              val (concreteArgs, condOpts) = params.zipWithIndex.map { case (v, i) =>
                if (!subset(v)) {
                  (args(i), Some(Equals(v.toVariable, exArgs(i))))
                } else {
                  (projections(v.getType), None)
                }
              }.unzip

              (concreteArgs, andJoin(condOpts.flatten))
            }).toSeq

          val withConds :+ ((concreteArgs, _)) = argumentsWithConds
          val default = extractValue(templates.mkApp(f, tpe, concreteArgs), tpe.to, nextSeen)

          val sortedArguments = withConds
            .groupBy(_._2)
            .view.mapValues(_.head._1)
            .toSeq
            .sortBy(p => -exprOps.formulaSize(p._1))

          val mappings = sortedArguments.map { case (cond, arguments) =>
            (cond, extractValue(templates.mkApp(f, tpe, arguments), tpe.to, nextSeen))
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
    inox.Model(program)(exModel.vars, exModel.chooses ++ chooses)
  }

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
      def cast(resp: SolverResponse[underlying.Model, Set[underlying.Trees]]): CheckResult =
        CheckResult(config.convert(config.cast(resp), extractSimpleModel, decodeAssumptions))

      def apply[M <: Model, A <: Assumptions](resp: config.Response[M, A]): CheckResult = resp match {
        case SatWithModel(_) if !checkModels && abort => new CheckResult(config cast Unknown)
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

    var currentState: CheckState = ModelCheck
    while (!currentState.isInstanceOf[CheckResult]) {
      currentState = currentState match {
        case Abort() =>
          CheckResult.cast(Unknown)

        case ModelCheck =>
          reporter.debug(" - Running search...")

          val getModel = !templates.requiresFiniteRangeCheck || checkModels || templates.hasAxioms
          val checkConfig = config
            .max(Configuration(model = getModel, unsatAssumptions = unrollAssumptions && templates.canUnroll))

          val res: SolverResponse[underlying.Model, Set[underlying.Trees]] = context.timers.solvers.unrolling.check.run {
            underlying.checkAssumptions(checkConfig)(
              encodedAssumptions.toSet ++ templates.satisfactionAssumptions
            )
          }

          reporter.debug(" - Finished search with blocked literals")

          res match {
            case Abort() =>
              CheckResult.cast(Unknown)

            case _: Satisfiable if templates.requiresFiniteRangeCheck =>
              FiniteRangeCheck

            case Sat =>
              CheckResult.cast(Sat)

            case SatWithModel(model) =>
              Validate(model)

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

          val res: SolverResponse[underlying.Model, Set[underlying.Trees]] = context.timers.solvers.unrolling.check.run {
            underlying.push()
            for (cl <- encodedAssumptions.toSeq ++ templates.satisfactionAssumptions ++ clauses) {
              underlying.assertCnstr(cl)
            }
            val res = underlying.check(Model)
            underlying.pop()
            res
          }

          reporter.debug(" - Finished checking finite ranges")

          res match {
            case Abort() =>
              CheckResult.cast(Unknown)

            case SatWithModel(model) =>
              Validate(model)

            case _ =>
              InstantiateQuantifiers
          }

        case Validate(umodel) =>
          (try { Some(extractTotalModel(umodel)) } catch {
            case NoSimpleValue(tpe) =>
              if (!silentErrors) {
                reporter.error("No simple value found for type " + tpe.asString)
              }
              None
            case Canceled() => None
          }).map { model =>
            lazy val sat = CheckResult(config cast (if (config.withModel) SatWithModel(model) else Sat))
            lazy val unknown = CheckResult cast Unknown

            val valid = !checkModels || validateModel(model, assumptionsSeq, silenceErrors = silentErrors)

            if (checkModels && valid) {
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
          }.getOrElse(CheckResult cast Unknown)

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
              underlying.checkAssumptions(config max Configuration(model = true))(
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
                CheckResult(config cast (if (config.withModel) SatWithModel(luckyModel.get) else Sat))
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

          reporter.debug(" - Finished unrolling")
          ModelCheck
        }

        case otherwise => sys.error(s"Unexpected case: $otherwise")
      }
    }

    val CheckResult(res) = currentState
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

  override lazy val name = "U:"+underlying.name

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

  protected lazy val modelEvaluator: DeterministicEvaluator { val program: self.targetProgram.type } =
    targetSemantics.getEvaluator(using context.withOpts(optIgnoreContracts(true)))

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
