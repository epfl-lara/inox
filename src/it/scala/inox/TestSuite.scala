/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import org.scalatest._
import org.scalatest.concurrent._

import utils._

trait TestSuite extends FunSuite with Matchers with TimeLimits {

  protected def configurations: Seq[Seq[OptionValue[_]]] = Seq(Seq.empty)

  protected def createContext(options: Options): Context = inox.TestContext(options)

  private val counter = new UniqueCounter[Unit]
  counter.nextGlobal // Start at 1

  protected def optionsString(options: Options): String = {
    "solvr=" + options.findOptionOrDefault(optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(solvers.unrolling.optFeelingLucky) + " " +
    "check=" + options.findOptionOrDefault(solvers.optCheckModels) + " " +
    "assum=" + options.findOptionOrDefault(solvers.unrolling.optUnrollAssumptions)
  }

  protected def test(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    test(name, _ => Test, tags : _*)(body)
  }

  sealed abstract class FilterStatus
  case object Test extends FilterStatus
  case object Ignore extends FilterStatus
  case object Skip extends FilterStatus
  case class WithContext(ctx: Context) extends FilterStatus

  protected def test(name: String, filter: Context => FilterStatus, tags: Tag*)(body: Context => Unit): Unit = {
    for (config <- configurations) {
      val ctx = createContext(Options(config))
      import ctx.reporter

      filter(ctx) match {
        case status @ (Test | Ignore | _: WithContext) =>
          val newCtx = status match {
            case WithContext(newCtx) => newCtx
            case _ => ctx
          }

          val index = counter.nextGlobal
          if (status == Ignore || newCtx.options.findOptionOrDefault(optSelectedSolvers).exists { sname =>
            (sname == "nativez3" || sname == "unrollz3" || sname == "nativez3-opt") && !solvers.SolverFactory.hasNativeZ3 ||
            (sname == "smt-z3" || sname == "smt-z3-opt") && !solvers.SolverFactory.hasZ3 ||
            sname == "smt-cvc4" && !solvers.SolverFactory.hasCVC4
          }) {
            super.ignore(f"$index%3d: $name ${optionsString(newCtx.options)}")(())
          } else {
            try {
              super.test(f"$index%3d: $name ${optionsString(newCtx.options)}")(body(newCtx))
            } catch {
              case err: FatalError =>
                reporter.error(err.msg)
                // If you got here while debugging the tests, use your debugger
                // to inspect the reporter (which should be of type TestSilentReporter)
                // "lastErrors" field.
                throw new exceptions.TestFailedException(err, 5)
            }
          }
        case Skip =>
      }
    }
  }

  protected def ignore(name: String, tags: Tag*)(body: Context => Unit): Unit = {
    test(name, _ => Ignore, tags : _*)(body)
  }

  protected def ignore(name: String, filter: Context => FilterStatus, tags: Tag*)(body: Context => Unit): Unit = {
    test(name, ctx => filter(ctx) match {
      case Skip => Skip
      case _ => Ignore
    }, tags : _*)(body)
  }
}
