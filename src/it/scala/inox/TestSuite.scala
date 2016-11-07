/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import org.scalatest._
import org.scalatest.concurrent._

import utils._

trait TestSuite extends FunSuite with Matchers with Timeouts {

  val configurations: Seq[Seq[OptionValue[_]]] = Seq(Seq.empty)

  private val counter = new UniqueCounter[Unit]
  counter.nextGlobal // Start at 1

  protected def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(solvers.unrolling.optFeelingLucky) + " " +
    "check=" + options.findOptionOrDefault(solvers.optCheckModels) + " " +
    "assum=" + options.findOptionOrDefault(solvers.unrolling.optUnrollAssumptions)
  }

  protected def test(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    for (config <- configurations) {
      val reporter = new TestSilentReporter
      val ctx = Context(reporter, new InterruptManager(reporter), Options(config))
      try {
        val index = counter.nextGlobal
        if (ctx.options.findOptionOrDefault(optSelectedSolvers).exists { sname =>
          (sname == "nativez3" || sname == "unrollz3") && !solvers.SolverFactory.hasNativeZ3 ||
          sname == "smt-z3" && !solvers.SolverFactory.hasZ3 ||
          sname == "smt-cvc4" && !solvers.SolverFactory.hasCVC4
        }) {
          super.ignore(f"$index%3d: $name ${optionsString(ctx.options)}")(())
        } else {
          super.test(f"$index%3d: $name ${optionsString(ctx.options)}")(body(ctx))
        }
      } catch {
        case err: FatalError =>
          reporter.lastErrors :+= err.msg
          throw new exceptions.TestFailedException(reporter.lastErrors.mkString("\n"), err, 5)
      }
    }
  }

  protected def ignore(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    for (config <- configurations) {
      val index = counter.nextGlobal
      super.ignore(f"$index%3d: $name ${optionsString(Options(config))}")(())
    }
  }
}
