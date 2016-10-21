/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import org.scalatest._
import org.scalatest.concurrent._

import utils._

trait InoxTestSuite extends FunSuite with Matchers with Timeouts {

  val configurations: Seq[Seq[OptionValue[_]]] = Seq(Seq.empty)

  private def optionsString(options: Options): String = {
    "solver=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "feelinglucky=" + options.findOptionOrDefault(solvers.unrolling.optFeelingLucky) + " " +
    "checkmodels=" + options.findOptionOrDefault(solvers.optCheckModels) + " " +
    "unrollassumptions=" + options.findOptionOrDefault(solvers.unrolling.optUnrollAssumptions)
  }

  protected def test(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    for (config <- configurations) {
      val reporter = new TestSilentReporter
      val ctx = Context(reporter, new InterruptManager(reporter), Options(config))
      try {
        super.test(name + " " + optionsString(ctx.options))(body(ctx))
      } catch {
        case err: FatalError =>
          reporter.lastErrors :+= err.msg
          throw new exceptions.TestFailedException(reporter.lastErrors.mkString("\n"), err, 5)
      }
    }
  }

  protected def ignore(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    for (config <- configurations) {
      super.ignore(name + " " + optionsString(Options(config)))(())
    }
  }
}
