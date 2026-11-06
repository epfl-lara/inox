/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class QuantifiersSuite extends ScriptTestSuite("quantifiers") {
  override protected def optionMatrix = List(
    (false, false, false),
    (true,  true,  false),
    (false, false, true ),
  ).map { case (checkModels, feelingLucky, unrollAssumptions) => Seq(
    optCheckModels(checkModels),
    optFeelingLucky(feelingLucky),
    optUnrollAssumptions(unrollAssumptions)
  )}

  // For this test, we do not check the generated model with the Princess solver as we
  // are not able to find a model that satisfies the idempotency requirement.
  // This is due to being unlucky in choosing a default value for the model of f.
  override protected def filter(ctx: Context, file: java.io.File): FilterStatus =
    if (file.getName == "commutative-idempotent.smt3" &&
        ctx.options.findOptionOrDefault(optSelectedSolvers) == Set("princess"))
      WithContext(ctx.withOpts(optCheckModels(false)))
    else Test
}
