/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import transformers._
import combinators._

/** Scala Native version of src/main/scala/inox/solvers/PlatformSolvers.scala:
  * the Z3 native interface (JNI), Princess and Eldarica need JVM-only
  * libraries, so the native build offers none of them. Requests for them
  * fall back to the SMT-LIB back ends, as when their library is missing.
  */
private[solvers] object PlatformSolvers {
  lazy val hasNativeZ3: Boolean = false

  // still accepted, so that scripts written for the JVM build keep working
  val solverNames: Map[String, String] = Map(
    "nativez3"     -> "Not available in the native build (falls back to smt-z3)",
    "nativez3-opt" -> "Not available in the native build (falls back to smt-z3-opt)",
    "unrollz3"     -> "Not available in the native build (falls back to smt-z3)",
  )

  val fallbacks: Map[String, (() => Boolean, Seq[String], String)] = Map(
    "nativez3"     -> (() => false, Seq("smt-z3", "smt-cvc4", "smt-cvc5"), "Z3 native interface"),
    "nativez3-opt" -> (() => false, Seq("smt-z3-opt"),                     "Z3 native interface"),
    "unrollz3"     -> (() => false, Seq("smt-z3", "smt-cvc4", "smt-cvc5"), "Z3 native interface"),
  )

  def getFromName(finalName: String, nonIncremental: Boolean)
                 (p: Program, ctx: Context)
                 (enc: ProgramTransformer {
                    val sourceProgram: p.type
                    val targetProgram: Program { val trees: inox.trees.type }
                  })(using sem: p.Semantics): Option[SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } }] =
    None
}
