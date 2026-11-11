/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** The semantics of function equality (see [[optFunctionEquality]]), as SMT-LIB 3 scripts that
  * select one with `(set-option :function-equality ...)`. Under `none` and `extensional`, distinct
  * functions have a distinguishing input in every model, which model checks verify.
  *
  * [[FunctionWitnessSuite]] checks what scripts can't: the shapes of models, and the rejection of
  * function comparisons under `none`.
  */
class FunctionSemanticsSuite extends ScriptTestSuite("function-semantics") {
  override protected def optionMatrix = UnrollingTestSuite.combinations(
    Seq(optCheckModels(true)),
    Seq(optModelFinding(0), optModelFinding(1))
  )
}
