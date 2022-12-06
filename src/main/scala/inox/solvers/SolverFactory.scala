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
    new SolverFactory {
      val program: p.type = p
      type S = S1 { val program: p.type }

      val name = nme
      def getNewSolver() = builder()
    }
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
    "smt-z3-min"    -> "Z3 minimizer through SMT-LIB",
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
    "smt-z3-min"   -> (() => hasZ3,       Seq("nativez3-opt"),                     "'z3' binary"),
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
                  })(implicit sem: p.Semantics): SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {

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
        new {
          val program: targetProgram.type = targetProgram
          val context = ctx
        } with NonIncrementalSolver {
          type Trees = T
          type Model = M
          val semantics: targetProgram.Semantics = targetSem
          def name = s"no-inc:$nme"

          def underlying() = underlyingSolver()
        }
      } else {
        underlyingSolver()
      }
    }


    finalName match {
      case "nativez3" => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        val fullEnc = enc andThen chooseEnc
        val theoryEnc = theories.Z3(fullEnc.targetProgram)
        val progEnc = fullEnc andThen theoryEnc
        val targetProg = progEnc.targetProgram

        () => new {
          val program: p.type = p
          val context = ctx
          val encoder: enc.type = enc
        } with z3.NativeZ3Solver with TimeoutSolver with tip.TipDebugger {
          override protected val semantics = sem
          override protected val chooses: chooseEnc.type = chooseEnc
          override protected lazy val theories: theoryEnc.type = theoryEnc
          override protected lazy val fullEncoder = fullEnc
          override protected lazy val programEncoder = progEnc
          override protected lazy val targetProgram: targetProg.type = targetProg
          override protected lazy val targetSemantics: targetProgram.Semantics = targetProgram.getSemantics
        }
      })

      case "nativez3-opt" => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        val fullEnc = enc andThen chooseEnc
        val theoryEnc = theories.Z3(fullEnc.targetProgram)
        val progEnc = fullEnc andThen theoryEnc
        val targetProg = progEnc.targetProgram

        () => new {
          val program: p.type = p
          val context = ctx
          val encoder: enc.type = enc
        } with z3.NativeZ3Optimizer with TimeoutSolver {
          override protected val semantics = sem
          override protected val chooses: chooseEnc.type = chooseEnc
          override protected lazy val theories: theoryEnc.type = theoryEnc
          override protected lazy val fullEncoder = fullEnc
          override protected lazy val programEncoder = progEnc
          override protected lazy val targetProgram: targetProg.type = targetProg
          override protected lazy val targetSemantics: targetProgram.Semantics = targetProgram.getSemantics
        }
      })

      case "unrollz3" => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        val fullEnc = enc andThen chooseEnc
        val theoryEnc = theories.Z3(fullEnc.targetProgram)
        val progEnc = fullEnc andThen theoryEnc
        val targetProg = progEnc.targetProgram
        val targetSem = targetProg.getSemantics

        () => new {
          val program: p.type = p
          val context = ctx
          val encoder: enc.type = enc
        } with UnrollingSolver with TimeoutSolver with tip.TipDebugger {
          override protected val semantics = sem
          override protected val chooses: chooseEnc.type = chooseEnc
          override protected val theories: theoryEnc.type = theoryEnc
          override protected lazy val fullEncoder = fullEnc
          override protected lazy val programEncoder = progEnc
          override protected lazy val targetProgram: targetProg.type = targetProg
          override protected val targetSemantics = targetSem

          protected val underlying = nonIncrementalWrap(progEnc.targetProgram)(finalName, targetSem, () => new {
            val program: progEnc.targetProgram.type = progEnc.targetProgram
            val context = ctx
          } with z3.UninterpretedZ3Solver {
            val semantics: program.Semantics = targetSem
          })
        }
      })

      case "smt-z3-opt" => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        val fullEnc = enc andThen chooseEnc
        val theoryEnc = theories.Z3(fullEnc.targetProgram)
        val progEnc = fullEnc andThen theoryEnc
        val targetProg = progEnc.targetProgram
        val targetSem = targetProg.getSemantics

        () => new {
          val program: p.type = p
          val context = ctx
          val encoder: enc.type = enc
        } with UnrollingOptimizer with TimeoutSolver {
          override protected val semantics = sem
          override protected val chooses: chooseEnc.type = chooseEnc
          override protected val theories: theoryEnc.type = theoryEnc
          override protected lazy val fullEncoder = fullEnc
          override protected lazy val programEncoder = progEnc
          override protected lazy val targetProgram: targetProg.type = targetProg
          override protected val targetSemantics = targetSem

          protected val underlying = new {
            val program: progEnc.targetProgram.type = progEnc.targetProgram
            val context = ctx
          } with smtlib.optimization.Z3Optimizer {
            val semantics: program.Semantics = targetSem
          }
        }
      })

      case "smt-z3-min" => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        val fullEnc = enc andThen chooseEnc
        val theoryEnc = theories.Z3(fullEnc.targetProgram)
        val progEnc = fullEnc andThen theoryEnc
        val targetProg = progEnc.targetProgram
        val targetSem = targetProg.getSemantics

        () => new {
          val program: p.type = p
          val context = ctx
          val encoder: enc.type = enc
        } with UnrollingOptimizer with TimeoutSolver {
          override protected val semantics = sem
          override protected val chooses: chooseEnc.type = chooseEnc
          override protected val theories: theoryEnc.type = theoryEnc
          override protected lazy val fullEncoder = fullEnc
          override protected lazy val programEncoder = progEnc
          override protected lazy val targetProgram: targetProg.type = targetProg
          override protected val targetSemantics = targetSem

          protected val underlying = new {
            val program: progEnc.targetProgram.type = progEnc.targetProgram
            val context = ctx
          } with smtlib.optimization.Z3Minimizer {
            val semantics: program.Semantics = targetSem
          }
        }
      })

      case _ if finalName == "smt-z3" || finalName.startsWith("smt-z3:") => create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        val fullEnc = enc andThen chooseEnc
        val theoryEnc = theories.Z3(fullEnc.targetProgram)
        val progEnc = fullEnc andThen theoryEnc
        val targetProg = progEnc.targetProgram
        val targetSem = targetProg.getSemantics
        val executableName = if (finalName == "smt-z3") "z3" else getZ3Executable(finalName)

        () => new {
          val program: p.type = p
          val context = ctx
          val encoder: enc.type = enc
        } with UnrollingSolver with TimeoutSolver with tip.TipDebugger {
          override protected val semantics = sem
          override protected val chooses: chooseEnc.type = chooseEnc
          override protected val theories: theoryEnc.type = theoryEnc
          override protected lazy val fullEncoder = fullEnc
          override protected lazy val programEncoder = progEnc
          override protected lazy val targetProgram: targetProg.type = targetProg
          override protected val targetSemantics = targetSem

          protected val underlying = nonIncrementalWrap(progEnc.targetProgram)(finalName, targetSem, () => new {
            val program: progEnc.targetProgram.type = progEnc.targetProgram
            val context = ctx
          } with smtlib.Z3Solver {
            val semantics: program.Semantics = targetSem
            override def targetName = executableName
          })
        }
      })

      case "smt-cvc4" => create(p)(finalName, {
        val ev = sem.getEvaluator(ctx)
        val chooseEnc = ChooseEncoder(p)(enc)
        val fullEnc = enc andThen chooseEnc
        val theoryEnc = theories.CVC4(fullEnc)(ev)
        val progEnc = fullEnc andThen theoryEnc
        val targetProg = progEnc.targetProgram
        val targetSem = targetProg.getSemantics

        () => new {
          val program: p.type = p
          val context = ctx
          val encoder: enc.type = enc
        } with UnrollingSolver with TimeoutSolver with tip.TipDebugger {
          override protected val semantics = sem
          override protected val chooses: chooseEnc.type = chooseEnc
          override protected val theories: theoryEnc.type = theoryEnc
          override protected lazy val fullEncoder = fullEnc
          override protected lazy val programEncoder = progEnc
          override protected lazy val targetProgram: targetProg.type = targetProg
          override protected val targetSemantics = targetSem

          protected val underlying = nonIncrementalWrap(progEnc.targetProgram)(finalName, targetSem, () => new {
            val program: progEnc.targetProgram.type = progEnc.targetProgram
            val context = ctx
          } with smtlib.CVC4Solver {
            val semantics: program.Semantics = targetSem
          })
        }
      })

      case "princess" => create(p)(finalName, {
        val ev = sem.getEvaluator(ctx)
        val chooseEnc = ChooseEncoder(p)(enc)
        val fullEnc = enc andThen chooseEnc
        val theoryEnc = theories.Princess(fullEnc)(ev)
        val progEnc = fullEnc andThen theoryEnc
        val targetProg = progEnc.targetProgram

        () => new {
          val program: p.type = p
          val context = ctx
          val encoder: enc.type = enc
        } with princess.PrincessSolver with TimeoutSolver {
          override protected val semantics = sem
          override protected val chooses: chooseEnc.type = chooseEnc
          override protected lazy val theories: theoryEnc.type = theoryEnc
          override protected lazy val fullEncoder = fullEnc
          override protected lazy val programEncoder = progEnc
          override protected lazy val targetProgram: targetProg.type = targetProg
          override protected lazy val targetSemantics: targetProgram.Semantics = targetProgram.getSemantics
        }
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
                      })(implicit sem: p.Semantics): SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
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
        val name = if (single.endsWith("-opt") || single.endsWith("-min")) single else single + "-opt"
        getFromName(name, force = solversOpt.isDefined)(p, ctx)(ProgramEncoder.empty(p))(p.getSemantics).asInstanceOf[SolverFactory {
          val program: p.type
          type S <: Optimizer with TimeoutSolver { val program: p.type }
        }]
      case multiple => throw FatalError("No support for portfolio optimizers")
    }
  }

  def apply(name: String, p: InoxProgram, ctx: Context, force: Boolean = false): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver { val program: p.type }
  } = getFromName(name, force = force)(p, ctx)(ProgramEncoder.empty(p))(p.getSemantics)

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
