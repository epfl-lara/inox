/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

/** Partial operations make the paths on which they fail infeasible, like errors, unless
  * `optAssumeChecked` holds. */
class PartialOperationsSuite extends ScriptTestSuite("partial-operations")
