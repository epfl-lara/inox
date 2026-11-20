/* Copyright 2009-2018 EPFL, Lausanne */

package inox

object TestContext {

  /** A context for `options`, under which the unrolling solvers check their clauses against the
    * rules that build them, unless `options` says otherwise (see [[solvers.unrolling.RuleChecker]]). */
  def apply(options: Options) = {
    val reporter = new TestSilentReporter
    val checked =
      if (options.findOption(solvers.unrolling.optCheckRules).isDefined) options
      else options + solvers.unrolling.optCheckRules(true)
    Context(reporter, new utils.InterruptManager(reporter), checked)
  }

  def empty = apply(Options.empty)
}
