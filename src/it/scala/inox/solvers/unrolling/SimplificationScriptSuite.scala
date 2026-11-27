/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** Queries whose simplifications take the paths that certificates check least often: quantifiers
  * in connectives, bindings, selections and arithmetic over terms that may fail, constructions of
  * sorts with invariants, the bodies of lambdas under extensional equality, and ground terms that
  * the simplifier evaluates. The certificates of their unsatisfiable queries are checked by the
  * survey of `CheckerSuite` too. */
class SimplificationScriptSuite extends ScriptTestSuite("simplifications")
