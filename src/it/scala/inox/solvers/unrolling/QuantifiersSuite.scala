/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package unrolling

class QuantifiersSuite extends ScriptTestSuite("quantifiers") {
  // The scripts only state specifications with their quantifiers, so they run whether
  // quantifiers are booleans or propositions.
  override protected def optionMatrix = for {
    (checkModels, feelingLucky, unrollAssumptions) <- List(
      (false, false, false),
      (true,  true,  false),
      (false, false, true ),
    )
    quantifiers <- ast.QuantifierMode.values.toSeq
  } yield Seq(
    optCheckModels(checkModels),
    optFeelingLucky(feelingLucky),
    optUnrollAssumptions(unrollAssumptions),
    ast.optQuantifiers(quantifiers)
  )

  override protected def optionsString(options: Options): String =
    super.optionsString(options) + " quant=" + options.findOptionOrDefault(ast.optQuantifiers).toString.toLowerCase

  // For this test, we do not check the generated model with the Princess solver as we
  // are not able to find a model that satisfies the idempotency requirement.
  // This is due to being unlucky in choosing a default value for the model of f.
  override protected def filter(ctx: Context, file: java.io.File): FilterStatus =
    if (file.getName == "commutative-idempotent.smt3" &&
        ctx.options.findOptionOrDefault(optSelectedSolvers) == Set("princess"))
      WithContext(ctx.withOpts(optCheckModels(false)))
    else Test
}
