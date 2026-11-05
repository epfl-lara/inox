/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import transformers._
import inox.solvers.invariant.AbstractInvariantSolver
import inox.solvers.invariant.InvariantSolver

/** The solver back ends that need JVM-only libraries: the Z3 native
  * interface (JNI), Princess and Eldarica. [[SolverFactory]] handles the
  * back ends that only need the Scala standard library and external solver
  * binaries, and falls back to this registry for the others.
  *
  * The Scala Native build of Inox (see `native/`) replaces this file with
  * an empty registry.
  */
private[solvers] object PlatformSolvers {
  import SolverFactory.{create, nonIncrementalWrap}
  import evaluators._
  import combinators._
  import unrolling._

  lazy val hasNativeZ3: Boolean = try {
    unpackZ3InNativeImage
    _root_.z3.Z3Wrapper.withinJar()
    true
  } catch {
    case _: java.lang.UnsatisfiedLinkError => false
    case _: java.lang.NoClassDefFoundError => false
    case _: java.io.IOException => false
  }

  /** ScalaZ3 unpacks its native libraries by reading its own jar file, which
    * a GraalVM native image doesn't have. It skips unpacking when the target
    * directory already exists, so in a native image we unpack the libraries
    * there ourselves, from the resources bundled into the image.
    */
  private lazy val unpackZ3InNativeImage: Unit =
    if (System.getProperty("org.graalvm.nativeimage.imagecode") != null) {
      import java.nio.file.{Files, Paths, StandardCopyOption}
      val dir = Paths.get(System.getProperty("java.io.tmpdir"),
        "SCALAZ3_" + _root_.z3.LibraryChecksum.value, "lib-bin")
      Files.createDirectories(dir)
      for (name <- Seq("z3", "z3java", "scalaz3")) {
        val lib = System.mapLibraryName(name)
        val target = dir.resolve(lib)
        if (!Files.exists(target)) {
          val in = getClass.getResourceAsStream("/lib-bin/" + lib)
          if (in != null) try {
            // Unpack next to the target and move it in place, so concurrent
            // runs never load a partially written library.
            val tmp = Files.createTempFile(dir, lib, ".tmp")
            Files.copy(in, tmp, StandardCopyOption.REPLACE_EXISTING)
            Files.move(tmp, target, StandardCopyOption.ATOMIC_MOVE)
          } finally in.close()
        }
      }
    }

  val solverNames: Map[String, String] = Map(
    "nativez3"      -> "Native Z3 with z3-templates for unrolling",
    "nativez3-opt"  -> "Native Z3 optimizer with z3-templates for unrolling",
    "unrollz3"      -> "Native Z3 with inox-templates for unrolling",
    "princess"      -> "Princess with inox unrolling",
    "inv-eld"       -> "Horn solver using Eldarica"
  )

  val fallbacks: Map[String, (() => Boolean, Seq[String], String)] = Map(
    "nativez3"     -> (() => hasNativeZ3, Seq("smt-z3", "smt-cvc4", "smt-cvc5", "princess"),   "Z3 native interface"),
    "nativez3-opt" -> (() => hasNativeZ3, Seq("smt-z3-opt"),                                   "Z3 native interface"),
    "unrollz3"     -> (() => hasNativeZ3, Seq("smt-z3", "smt-cvc4", "smt-cvc5", "princess"),   "Z3 native interface"),
    "inv-eld"      -> (() => true,        Seq(),                                               "Eldarica solver"),
    "princess"     -> (() => true,        Seq(),                                               "Princess solver")
  )

  def getFromName(finalName: String, nonIncremental: Boolean)
                 (p: Program, ctx: Context)
                 (enc: ProgramTransformer {
                    val sourceProgram: p.type
                    val targetProgram: Program { val trees: inox.trees.type }
                  })(using sem: p.Semantics): Option[SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } }] = {
    if (finalName.contains("z3")) unpackZ3InNativeImage
    finalName match {
      case "nativez3" => Some(create(p)(finalName, {
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
      }))

      case "nativez3-opt" => Some(create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        // Override of `program` is needed as we need to have `program: p.type`
        class NativeZ3OptImpl(override val program: p.type)
          extends z3.Z3Unrolling(program)(program, ctx, enc, chooseEnc) with z3.NativeZ3Optimizer with TimeoutSolver

        () => new NativeZ3OptImpl(p)
      }))

      case "unrollz3" => Some(create(p)(finalName, {
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

          protected val underlying = nonIncrementalWrap(ctx, nonIncremental)(targetProgram)(finalName, targetSemantics, () => new Underlying(targetProgram))

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = enc
        }

        () => new UnrollZ3Impl(p)(enc)(ChooseEncoder(p)(enc))
      }))

      case "inv-eld" => Some(create(p)(finalName, {
        val emptyEnc = ProgramEncoder.empty(enc.targetProgram)
        val chooses = ChooseEncoder(enc.targetProgram)(emptyEnc)
        class SMTEldaricaImpl(override val program: enc.targetProgram.type)
          extends AbstractInvariantSolver (program, ctx)(program)(emptyEnc)(emptyEnc)(using program.getSemantics, emptyEnc.targetProgram.getSemantics)
            with InvariantSolver
            with TimeoutSolver
            with tip.TipDebugger {

          override val name = "inv-eld" 

          class Underlying(override val program: targetProgram.type)
            extends smtlib.SMTLIBSolver(program, context)
              with smtlib.EldaricaSolver

          override protected val underlyingHorn = Underlying(targetProgram)

          // encoder is from TipDebugger and enc from AbstractUnrollingSolver
          override protected val encoder = emptyEnc
        }

        class EncodedImpl(program: p.type, enc: transformers.ProgramTransformer {
                         val sourceProgram: program.type
                         val targetProgram: Program { val trees: inox.trees.type }
                       }, underlying: Solver {val program: enc.targetProgram.type}) 
              extends EncodingSolver(program, enc, underlying) with TimeoutSolver

        () => new EncodedImpl(p, enc, SMTEldaricaImpl(enc.targetProgram))
      }))

      case "princess" => Some(create(p)(finalName, {
        val chooseEnc = ChooseEncoder(p)(enc)
        class PrincessImpl(override val program: p.type)
          extends princess.PrincessSolver(p)(p, ctx, enc, chooseEnc) with TimeoutSolver

        () => new PrincessImpl(p)
      }))

      case _ => None
    }
  }
}
