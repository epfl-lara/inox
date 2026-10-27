/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class FunctionEqualitySuite extends ScriptTestSuite("function-equality") {
  // these tests compare functions structurally
  override def configurations = super.configurations.map(_ :+ optFunctionEquality(FunctionEquality.Intensional))
}
