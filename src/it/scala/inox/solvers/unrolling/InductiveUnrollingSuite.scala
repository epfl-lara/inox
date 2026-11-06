/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class InductiveUnrollingSuite extends ScriptTestSuite("inductive-unrolling") {

  override protected def filter(ctx: Context, file: java.io.File): FilterStatus = {
    val (allowSelect, allowOpt) = file.getName match {
      case "size-zero.smt3" | "size-negative.smt3" => return Test
      case "flatmap-is-associative.smt3" => (true, true)
      case "sort-preserves-content-2.smt3" => (false, false)
      case _ => (true, false)
    }
    val solvers = ctx.options.findOptionOrDefault(optSelectedSolvers)
    val feelingLucky = ctx.options.findOptionOrDefault(optFeelingLucky)
    val checkModels = ctx.options.findOptionOrDefault(optCheckModels)
    val unrollAssume = ctx.options.findOptionOrDefault(optUnrollAssumptions)
    if (solvers == Set("princess") &&
      (!allowSelect || feelingLucky != checkModels || checkModels != unrollAssume)) Skip
    else if (solvers == Set("nativez3-opt") && !allowOpt) Skip
    else Test
  }
}
