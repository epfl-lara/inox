/* Copyright 2009-2016 EPFL, Lausanne */

package inox

object TestContext {

  def apply(options: Options) = {
    val reporter = new TestSilentReporter
    Context(reporter, new utils.InterruptManager(reporter), options)
  }

  def empty = apply(Options.empty)
}
