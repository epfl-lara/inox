/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import transformers._
import inox.solvers.evaluating.EvaluatingSolver
import inox.solvers.invariant.AbstractInvariantSolver
import inox.solvers.invariant.InvariantSolver

trait SolverFactory {
  val program: Program

  type S <: Solver { val program: SolverFactory.this.program.type }

  val name: String

  def getNewSolver(): S

  def shutdown(): Unit = {}

  def reclaim(s: S): Unit = {
    s.free()
  }

  def toAPI = SimpleSolverAPI(this)
}

object SolverFactory {

  lazy val hasNativeZ3: Boolean = PlatformSolvers.hasNativeZ3

  import _root_.smtlib.interpreters._

  lazy val hasZ3 = try {
    new Z3Interpreter("z3", Array("-in", "-smt2")).interrupt()
    true
  } catch {
    case _: java.io.IOException => false
  }

  lazy val hasCVC4 = try {
    new CVC4Interpreter("cvc4", Array("-q", "--lang", "smt2.6")).interrupt()
    true
  } catch {
    case _: java.io.IOException => false
  }

  lazy val hasCVC5 = try {
    new CVC5Interpreter("cvc5", Array("-q", "--lang", "smt2.6")).interrupt()
    true
  } catch {
    case _: java.io.IOException => false
  }

  lazy val hasBitwuzla = try {
    new BitwuzlaInterpreter("bitwuzla", Array("-v", "0", "--lang", "smt2")).interrupt()
    true
  } catch {
    case _: java.io.IOException => false
  }

  def create[S1 <: Solver](p: Program)(nme: String, builder: () => S1 { val program: p.type }):
           SolverFactory { val program: p.type; type S = S1 { val program: p.type } } = {
    class Impl(override val program: p.type, override val name: String) extends SolverFactory {
      type S = S1 { val program: p.type }
      def getNewSolver() = builder()
    }
    new Impl(p, nme)
  }

  import evaluators._
  import combinators._
  import unrolling._

  val solverNames: Map[String, String] = PlatformSolvers.solverNames ++ Map(
    "smt-cvc4"      -> "CVC4 through SMT-LIB",
    "smt-cvc5"      -> "cvc5 through SMT-LIB",
    "smt-z3"        -> "Z3 through SMT-LIB",
    "smt-z3-opt"    -> "Z3 optimizer through SMT-LIB",
    "smt-z3:<exec>" -> "Z3 through SMT-LIB with custom executable name",
    "smt-bitwuzla"  -> "Bitwuzla through SMT-LIB",
    "eval"          -> "Internal evaluator to discharge ground assertions",
    "inv-z3"        -> "Horn solver using Z3 / Spacer",

  )

  private val fallbacks: Map[String, (() => Boolean, Seq[String], String)] = PlatformSolvers.fallbacks ++ Map(
    "inv-z3"       -> (() => hasZ3,       Seq("smt-z3", "smt-cvc4", "smt-cvc5", "princess"),   "Z3 native interface"),
    "smt-cvc4"     -> (() => hasCVC4,     Seq("nativez3", "smt-z3", "princess"),               "'cvc4' binary"),
    "smt-cvc5"     -> (() => hasCVC5,     Seq("nativez3", "smt-z3", "princess"),               "'cvc5' binary"),
    "smt-z3"       -> (() => hasZ3,       Seq("nativez3", "smt-cvc4", "smt-cvc5", "princess"), "'z3' binary"),
    "smt-z3-opt"   -> (() => hasZ3,       Seq("nativez3-opt"),                                 "'z3' binary"),
    "eval"         -> (() => true,        Seq(),                                               "Internal evaluator"),
    "smt-bitwuzla" -> (() => hasBitwuzla, Seq("smt-cvc5", "nativez3", "smt-z3", "princess"),   "'bitwuzla' binary"),
  )

  private var reported: Boolean = false

  /** Wraps a solver factory into a [[NonIncrementalSolver]] when `nonIncremental` is set. */
  private[solvers] def nonIncrementalWrap[T, M](ctx: Context, nonIncremental: Boolean)(targetProgram: Program)(
    nme: String,
    targetSem: targetProgram.Semantics,
    underlyingSolver: () => AbstractSolver {
      val program: targetProgram.type
      type Trees = T
      type Model = M
  }): AbstractSolver {
        val program: targetProgram.type
        type Trees = T
        type Model = M
      } = {

    if (nonIncremental) {
      class NonIncrementalImpl(override val program: targetProgram.type, override val context: inox.Context)
        extends NonIncrementalSolver {
        override type Trees = T
        override type Model = M
        override def name = s"no-inc:$nme"
        override def underlying() = underlyingSolver()
      }
      new NonIncrementalImpl(targetProgram, ctx)
    } else {
      underlyingSolver()
    }
  }

  // extract <exec> in "smt-z3:<exec>"
  private def getZ3Executable(name: String): String = name.drop(7)

  // extract solver in "no-inc:solver"
  private def removeNoInc(name: String): String = name.drop(7)

  /** The solvers operate under `model`, as when an evaluator solves for the foralls and chooses of an
    * expression that it evaluates in this model. Only the unrolling solvers can operate under a
    * model that interprets functions. */
  def getFromName(name: String, force: Boolean = false)
                 (p: Program, ctx: Context, model: Option[p.Model] = None)
                 (enc: ProgramTransformer {
                    val sourceProgram: p.type
                    val targetProgram: Program { val trees: inox.trees.type }
                  })(using sem: p.Semantics): SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    val solverModel = model.getOrElse(inox.Model.empty(p))
    val nonIncremental = name.startsWith("no-inc:")
    val noPrefixName = if (nonIncremental) removeNoInc(name) else name

    if (
      nonIncremental &&
      noPrefixName != "smt-cvc4" &&
      noPrefixName != "smt-cvc5" &&
      noPrefixName != "unrollz3" &&
      noPrefixName != "smt-z3" &&
      !noPrefixName.startsWith("smt-z3:")
    )
      throw FatalError(s"Non incremental mode is not available for solver $name")

    val finalName = if (force) {
      noPrefixName
    } else {
      fallbacks.get(noPrefixName) match {
        case Some((guard, names, requirement)) if !guard() =>
          val replacement = names.collectFirst {
            case name if fallbacks.get(name).exists(_._1()) => name
          }.getOrElse(ctx.reporter.fatalError(s"No fallback available for solver $name"))

          if (!reported) {
            ctx.reporter.warning(s"The $requirement is not available. Falling back onto $replacement.")
            reported = true
          }
          replacement

        case Some(_) => noPrefixName
        case None if noPrefixName.startsWith("smt-z3:") =>
          val z3Exec = getZ3Executable(noPrefixName)
          val hasZ3Exec = try {
            new Z3Interpreter(z3Exec, Array("-in", "-smt2")).interrupt()
            true
          } catch {
            case _: java.io.IOException => false
          }

          if (hasZ3Exec) noPrefixName
          else throw FatalError("Unknown solver: " + z3Exec)

        case _ => throw FatalError("Unknown solver: " + noPrefixName)
      }
    }

    if (solverModel.chooses.nonEmpty && Set("inv-z3", "inv-eld", "eval")(finalName))
      throw FatalError(s"Solver $finalName can't operate under a model that interprets functions")

    finalName match {
      case "smt-z3-opt" => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        class SMTZ3OptImpl(override val program: p.type)
          extends AbstractUnrollingSolver(program, ctx, enc, chooseEnc)(fullEncoder => theories.Z3(fullEncoder.targetProgram))
            with UnrollingOptimizer
            with TimeoutSolver {

          class Underlying(override val program: targetProgram.type)
            extends smtlib.SMTLIBSolver(targetProgram, ctx)
              with smtlib.optimization.Z3Optimizer

          protected val underlying = new Underlying(targetProgram)

          override protected def partialModel = solverModel
        }

        () => new SMTZ3OptImpl(p)
      })

      case "inv-z3" => create(p)(finalName, {
        val emptyEnc = ProgramEncoder.empty(enc.targetProgram)
        val chooses = ChooseEncoder(enc.targetProgram)(emptyEnc)
        class SMTZ3Impl(override val program: enc.targetProgram.type)
          extends AbstractInvariantSolver (program, ctx)(program)(emptyEnc)(emptyEnc)(using program.getSemantics, emptyEnc.targetProgram.getSemantics)
            with InvariantSolver
            with TimeoutSolver
            with tip.TipDebugger {

          override val name = "inv-z3" 

          class Underlying(override val program: targetProgram.type)
            extends smtlib.SMTLIBSolver(program, context)
              with smtlib.Z3Solver {
            override def targetName = "z3"
            import _root_.smtlib.trees.Terms
            import _root_.smtlib.trees.CommandsResponses._
            import _root_.smtlib.trees.Commands._
            import _root_.smtlib.Interpreter
            import _root_.smtlib.printer.Printer
            import _root_.smtlib.printer.RecursivePrinter
            import java.io.BufferedReader
            import _root_.smtlib.interpreters.ProcessInterpreter
            import _root_.smtlib.parser.Parser
            import _root_.smtlib.extensions.tip.Lexer

            class  HornZ3Interpreter(executable: String,
                              args: Array[String],
                              printer: Printer = RecursivePrinter,
                              parserCtor: BufferedReader => Parser = out => new Parser(new Lexer(out)))
            extends ProcessInterpreter (executable, args, printer, parserCtor):
              printer.printCommand(SetOption(PrintSuccess(true)), in)
              in.write("\n")
              in.flush()
              parser.parseGenResponse
              in.write("(set-logic HORN)\n")
              in.flush()
              parser.parseGenResponse

              override def eval(cmd: Terms.SExpr): Terms.SExpr = 
                super.eval(cmd)

            override protected val interpreter = {
              val opts = interpreterOpts
              // reporter.debug("Invoking solver "+targetName+" with "+opts.mkString(" "))
              new HornZ3Interpreter(targetName, opts.toArray, parserCtor = out => new Z3Parser(new Lexer(out)))
            }

            // the interpreter sets the logic when it starts, and a reset forgets it
            override protected def initialize(): Unit =
              emit(SetLogic(NonStandardLogic(Terms.SSymbol("HORN"))))
          }

          override protected val underlyingHorn = Underlying(targetProgram)

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = emptyEnc
        }

        class EncodedImpl(program: p.type, enc: transformers.ProgramTransformer {
                         val sourceProgram: program.type
                         val targetProgram: Program { val trees: inox.trees.type }
                       }, underlying: Solver {val program: enc.targetProgram.type}) 
              extends EncodingSolver(program, enc, underlying) with TimeoutSolver

        () => new EncodedImpl(p, enc, SMTZ3Impl(enc.targetProgram))
      })

      case _ if finalName == "smt-z3" || finalName.startsWith("smt-z3:") => create(p)(finalName, {
        class SMTZ3Impl(override val program: p.type)
                       (override val enc: transformers.ProgramTransformer {
                         val sourceProgram: program.type
                         val targetProgram: Program { val trees: inox.trees.type }
                       })
                       (override val chooses: ChooseEncoder {
                         val program: p.type
                         val sourceEncoder: enc.type
                       })
          extends AbstractUnrollingSolver(program, ctx, enc, chooses)(fullEncoder => theories.Z3(fullEncoder.targetProgram))
            with UnrollingSolver
            with TimeoutSolver
            with tip.TipDebugger {

          class Underlying(override val program: targetProgram.type)
            extends smtlib.SMTLIBSolver(program, context)
              with smtlib.Z3Solver {
            override def targetName = if (finalName == "smt-z3") "z3" else getZ3Executable(finalName)
          }

          override protected val underlying =
            nonIncrementalWrap(ctx, nonIncremental)(targetProgram)(finalName, targetSemantics, () => new Underlying(targetProgram))

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = enc

          // Used to report SMT Lib files <-> VCs correspondence
          override def getSmtLibFileId: Option[Int] = underlying.getSmtLibFileId

          override protected def partialModel = solverModel
        }

        () => new SMTZ3Impl(p)(enc)(ChooseEncoder(p)(enc))
      })

      case "smt-cvc4" => create(p)(finalName, {
        val ev = sem.getEvaluator(using ctx)
        class SMTCVC4Impl(override val program: p.type)
                         (override val enc: transformers.ProgramTransformer {
                           val sourceProgram: program.type
                           val targetProgram: Program { val trees: inox.trees.type }
                         })
                         (override val chooses: ChooseEncoder {
                           val program: p.type
                           val sourceEncoder: enc.type
                         })
          extends AbstractUnrollingSolver(program, ctx, enc, chooses)(fullEncoder => theories.CVC(fullEncoder)(ev))
            with UnrollingSolver
            with TimeoutSolver
            with tip.TipDebugger {

          class Underlying(override val program: targetProgram.type)
            extends smtlib.SMTLIBSolver(program, ctx)
              with smtlib.CVC4Solver

          protected val underlying = nonIncrementalWrap(ctx, nonIncremental)(targetProgram)(finalName, targetSemantics, () => new Underlying(targetProgram))

          // Used to report SMT Lib files <-> VCs correspondence
          override def getSmtLibFileId: Option[Int] = underlying.getSmtLibFileId

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = enc

          override protected def partialModel = solverModel
        }

        () => new SMTCVC4Impl(p)(enc)(ChooseEncoder(p)(enc))
      })

      case "smt-cvc5" => create(p)(finalName, {
        val ev = sem.getEvaluator(using ctx)
        class SMTCVC5Impl(override val program: p.type)
                         (override val enc: transformers.ProgramTransformer {
                           val sourceProgram: program.type
                           val targetProgram: Program { val trees: inox.trees.type }
                         })
                         (override val chooses: ChooseEncoder {
                           val program: p.type
                           val sourceEncoder: enc.type
                         })
          extends AbstractUnrollingSolver(program, ctx, enc, chooses)(fullEncoder => theories.CVC(fullEncoder)(ev))
            with UnrollingSolver
            with TimeoutSolver
            with tip.TipDebugger {

          class Underlying(override val program: targetProgram.type)
            extends smtlib.SMTLIBSolver(program, ctx)
              with smtlib.CVC5Solver

          protected val underlying = nonIncrementalWrap(ctx, nonIncremental)(targetProgram)(finalName, targetSemantics, () => new Underlying(targetProgram))

          // Used to report SMT Lib files <-> VCs correspondence
          override def getSmtLibFileId: Option[Int] = underlying.getSmtLibFileId
          
          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = enc

          override protected def partialModel = solverModel
        }

        () => new SMTCVC5Impl(p)(enc)(ChooseEncoder(p)(enc))
      })

      case "smt-bitwuzla" => create(p)(finalName, {
        val ev = sem.getEvaluator(using ctx)
        class SMTBitwuzlaImpl(override val program: p.type)
                         (override val enc: transformers.ProgramTransformer {
                           val sourceProgram: program.type
                           val targetProgram: Program { val trees: inox.trees.type }
                         })
                         (override val chooses: ChooseEncoder {
                           val program: p.type
                           val sourceEncoder: enc.type
                         })
          extends AbstractUnrollingSolver(program, ctx, enc, chooses)(fullEncoder => theories.CVC(fullEncoder)(ev))
            with UnrollingSolver
            with TimeoutSolver
            with tip.TipDebugger {

          class Underlying(override val program: targetProgram.type)
            extends smtlib.SMTLIBSolver(program, ctx)
              with smtlib.BitwuzlaSolver

          protected val underlying = nonIncrementalWrap(ctx, nonIncremental)(targetProgram)(finalName, targetSemantics, () => new Underlying(targetProgram))

          // Used to report SMT Lib files <-> VCs correspondence
          override def getSmtLibFileId: Option[Int] = underlying.getSmtLibFileId

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = enc

          override protected def partialModel = solverModel
        }

        () => new SMTBitwuzlaImpl(p)(enc)(ChooseEncoder(p)(enc))
      })

      case "eval" => create(p)(finalName, {
        val encAlias = enc // alias to resolve ambiguous reference
        class EvalImpl(override val program: p.type) extends EvaluatingSolver(p, ctx)(p)(enc)(enc) with TimeoutSolver with tip.TipDebugger:
          override protected val encoder = encAlias // for tip debugger

        () => new EvalImpl(p)
      })

      case _ => PlatformSolvers.getFromName(finalName, nonIncremental)(p, ctx, solverModel)(enc)
        .getOrElse(throw FatalError("Unknown solver: " + finalName))
    }
  }

  def supportedSolver(s: String) =
    solverNames.contains(s) ||
    s.startsWith("smt-z3:") ||
    s.startsWith("no-inc:smt-z3:") ||
    s == "no-inc:smt-z3" ||
    s == "no-inc:smt-cvc4" ||
    s == "no-inc:smt-cvc5" ||
    s == "no-inc:unrollz3"

  def getFromSettings(p: Program, ctx: Context, model: Option[p.Model] = None)
                     (enc: ProgramTransformer {
                        val sourceProgram: p.type
                        val targetProgram: Program { val trees: inox.trees.type }
                      })(using sem: p.Semantics): SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    ctx.options.findOption(optSelectedSolvers) match {
      case None => optSelectedSolvers.default.toSeq match {
        case Seq() => throw FatalError("No selected solver")
        case Seq(single) => getFromName(single, force = false)(p, ctx, model)(enc)
        case multiple => PortfolioSolverFactory(p) {
          multiple.map(name => getFromName(name, force = false)(p, ctx, model)(enc))
        }
      }

      case Some(set) => set.toSeq match {
        case Seq() => throw FatalError("No selected solver")
        case Seq(single) => getFromName(single, force = true)(p, ctx, model)(enc)
        case multiple => PortfolioSolverFactory(p) {
          multiple.map(name => getFromName(name, force = true)(p, ctx, model)(enc))
        }
      }
    }
  }

  def optimizer(p: InoxProgram, ctx: Context): SolverFactory {
    val program: p.type
    type S <: Optimizer & TimeoutSolver { val program: p.type }
  } = {
    val solversOpt = ctx.options.findOption(optSelectedSolvers)
    (solversOpt getOrElse optSelectedSolvers.default).toSeq match {
      case Seq() => throw FatalError("No selected solver")
      case Seq(single) =>
        val name = if (single.endsWith("-opt")) single else single + "-opt"
        getFromName(name, force = solversOpt.isDefined)(p, ctx)(ProgramEncoder.empty(p))(using p.getSemantics).asInstanceOf[SolverFactory {
          val program: p.type
          type S <: Optimizer & TimeoutSolver { val program: p.type }
        }]
      case multiple => throw FatalError("No support for portfolio optimizers")
    }
  }

  def apply(name: String, p: InoxProgram, ctx: Context, force: Boolean = false): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver { val program: p.type }
  } = getFromName(name, force = force)(p, ctx)(ProgramEncoder.empty(p))(using p.getSemantics)

  def apply(p: InoxProgram, ctx: Context): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver { val program: p.type }
  } = ctx.options.findOption(optSelectedSolvers) match {
    case None => optSelectedSolvers.default.toSeq match {
      case Seq() => throw FatalError("No selected solver")
      case Seq(single) => apply(single, p, ctx, force = false)
      case multiple => PortfolioSolverFactory(p) {
        multiple.map(name => apply(name, p, ctx, force = false))
      }
    }

    case Some(set) => set.toSeq match {
      case Seq() => throw FatalError("No selected solver")
      case Seq(single) => apply(single, p, ctx, force = true)
      case multiple => PortfolioSolverFactory(p) {
        multiple.map(name => apply(name, p, ctx, force = true))
      }
    }
  }
}
