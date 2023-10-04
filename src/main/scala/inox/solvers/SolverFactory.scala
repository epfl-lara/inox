/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers

import transformers._

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

  lazy val hasNativeZ3 = try {
    _root_.z3.Z3Wrapper.withinJar()
    true
  } catch {
    case _: java.lang.UnsatisfiedLinkError => false
    case _: java.lang.NoClassDefFoundError => false
  }

  import _root_.smtlib.interpreters._

  lazy val hasZ3 = try {
    new Z3Interpreter("z3", Array("-in", "-smt2")).interrupt()
    true
  } catch {
    case _: java.io.IOException => false
  }

  lazy val hasCVC4 = try {
    new CVC4Interpreter("cvc4", Array("-q", "--lang", "smt2.5")).interrupt()
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

  val solverNames = Map(
    "nativez3"      -> "Native Z3 with z3-templates for unrolling",
    "nativez3-opt"  -> "Native Z3 optimizer with z3-templates for unrolling",
    "unrollz3"      -> "Native Z3 with inox-templates for unrolling",
    "smt-cvc4"      -> "CVC4 through SMT-LIB",
    "smt-z3"        -> "Z3 through SMT-LIB",
    "smt-z3-opt"    -> "Z3 optimizer through SMT-LIB",
    "smt-z3:<exec>" -> "Z3 through SMT-LIB with custom executable name",
    "princess"      -> "Princess with inox unrolling"
  )

  private val fallbacks = Map(
    "nativez3"     -> (() => hasNativeZ3, Seq("smt-z3", "smt-cvc4",   "princess"), "Z3 native interface"),
    "nativez3-opt" -> (() => hasNativeZ3, Seq("smt-z3-opt"),                       "Z3 native interface"),
    "unrollz3"     -> (() => hasNativeZ3, Seq("smt-z3", "smt-cvc4",   "princess"), "Z3 native interface"),
    "smt-cvc4"     -> (() => hasCVC4,     Seq("nativez3", "smt-z3",   "princess"), "'cvc4' binary"),
    "smt-z3"       -> (() => hasZ3,       Seq("nativez3", "smt-cvc4", "princess"), "'z3' binary"),
    "smt-z3-opt"   -> (() => hasZ3,       Seq("nativez3-opt"),                     "'z3' binary"),
    "princess"     -> (() => true,        Seq(),                                   "Princess solver")
  )

  private var reported: Boolean = false

  // extract <exec> in "smt-z3:<exec>"
  private def getZ3Executable(name: String): String = name.drop(7)

  // extract solver in "no-inc:solver"
  private def removeNoInc(name: String): String = name.drop(7)

  def getFromName(name: String, force: Boolean = false)
                 (p: Program, ctx: Context)
                 (enc: ProgramTransformer {
                    val sourceProgram: p.type
                    val targetProgram: Program { val trees: inox.trees.type }
                  })(using sem: p.Semantics): SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    val nonIncremental = name.startsWith("no-inc:")
    val noPrefixName = if (nonIncremental) removeNoInc(name) else name

    if (
      nonIncremental &&
      noPrefixName != "smt-cvc4" &&
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
            case name if fallbacks(name)._1() => name
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

    def nonIncrementalWrap[T, M](targetProgram: Program)(
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


    finalName match {
      case "nativez3" => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        class NativeZ3Impl(override val program: p.type)
                          (override val enc: transformers.ProgramTransformer {
                            val sourceProgram: program.type
                            val targetProgram: Program { val trees: inox.trees.type }
                          })
                          (override val chooses: ChooseEncoder {
                            val program: p.type
                            val sourceEncoder: enc.type
                          })
          extends z3.NativeZ3Solver(program)(program, ctx, enc, chooses)
            with TimeoutSolver
            with tip.TipDebugger {

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = enc
        }
        () => new NativeZ3Impl(p)(enc)(chooseEnc)
      })

      case "nativez3-opt" => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        // Override of `program` is needed as we need to have `program: p.type`
        class NativeZ3OptImpl(override val program: p.type)
          extends z3.Z3Unrolling(program)(program, ctx, enc, chooseEnc) with z3.NativeZ3Optimizer with TimeoutSolver

        () => new NativeZ3OptImpl(p)
      })

      case "unrollz3" => create(p)(finalName, {
        class UnrollZ3Impl(override val program: p.type)
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
            with tip.TipDebugger { self =>

          class Underlying(override val program: targetProgram.type)
            extends z3.UninterpretedZ3Solver(targetProgram, ctx)

          protected val underlying = nonIncrementalWrap(targetProgram)(finalName, targetSemantics, () => new Underlying(targetProgram))

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = enc
        }

        () => new UnrollZ3Impl(p)(enc)(ChooseEncoder(p)(enc))
      })

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
        }

        () => new SMTZ3OptImpl(p)
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
            nonIncrementalWrap(targetProgram)(finalName, targetSemantics, () => new Underlying(targetProgram))

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = enc
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
          extends AbstractUnrollingSolver(program, ctx, enc, chooses)(fullEncoder => theories.CVC4(fullEncoder)(ev))
            with UnrollingSolver
            with TimeoutSolver
            with tip.TipDebugger {

          class Underlying(override val program: targetProgram.type)
            extends smtlib.SMTLIBSolver(program, ctx)
              with smtlib.CVC4Solver

          protected val underlying = nonIncrementalWrap(targetProgram)(finalName, targetSemantics, () => new Underlying(targetProgram))

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = enc
        }

        () => new SMTCVC4Impl(p)(enc)(ChooseEncoder(p)(enc))
      })

      case "princess" => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        class PrincessImpl(override val program: p.type)
          extends princess.PrincessSolver(p)(p, ctx, enc, chooseEnc) with TimeoutSolver

        () => new PrincessImpl(p)
      })

      case _ => throw FatalError("Unknown solver: " + finalName)
    }
  }

  def supportedSolver(s: String) =
    solverNames.contains(s) ||
    s.startsWith("smt-z3:") ||
    s.startsWith("no-inc:smt-z3:") ||
    s == "no-inc:smt-z3" ||
    s == "no-inc:smt-cvc4" ||
    s == "no-inc:unrollz3"

  def getFromSettings(p: Program, ctx: Context)
                     (enc: ProgramTransformer {
                        val sourceProgram: p.type
                        val targetProgram: Program { val trees: inox.trees.type }
                      })(using sem: p.Semantics): SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    ctx.options.findOption(optSelectedSolvers) match {
      case None => optSelectedSolvers.default.toSeq match {
        case Seq() => throw FatalError("No selected solver")
        case Seq(single) => getFromName(single, force = false)(p, ctx)(enc)
        case multiple => PortfolioSolverFactory(p) {
          multiple.map(name => getFromName(name, force = false)(p, ctx)(enc))
        }
      }

      case Some(set) => set.toSeq match {
        case Seq() => throw FatalError("No selected solver")
        case Seq(single) => getFromName(single, force = true)(p, ctx)(enc)
        case multiple => PortfolioSolverFactory(p) {
          multiple.map(name => getFromName(name, force = true)(p, ctx)(enc))
        }
      }
    }
  }

  def optimizer(p: InoxProgram, ctx: Context): SolverFactory {
    val program: p.type
    type S <: Optimizer with TimeoutSolver { val program: p.type }
  } = {
    val solversOpt = ctx.options.findOption(optSelectedSolvers)
    (solversOpt getOrElse optSelectedSolvers.default).toSeq match {
      case Seq() => throw FatalError("No selected solver")
      case Seq(single) =>
        val name = if (single.endsWith("-opt")) single else single + "-opt"
        getFromName(name, force = solversOpt.isDefined)(p, ctx)(ProgramEncoder.empty(p))(using p.getSemantics).asInstanceOf[SolverFactory {
          val program: p.type
          type S <: Optimizer with TimeoutSolver { val program: p.type }
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
