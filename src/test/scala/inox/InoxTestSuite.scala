/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import org.scalatest._
import org.scalatest.concurrent._

trait InoxTestSuite extends FunSuite with Timeouts {
  type FixtureParam = InoxContext

  val configurations: Seq[Seq[InoxOption[Any]]] = Seq(Seq.empty)

  protected def test(name: String, tags: Tag*)(test: InoxContext => Outcome): Unit = {
    for (config <- configurations) {
      val reporter = new TestSilentReporter
      val ctx = InoxContext(reporter, new InterruptManager(reporter), InoxOptions(config))
      try {
        test(ctx)
      } catch {
        case err: FatalError =>
          reporter.lastErrors ++= err.msg
          Failed(new exceptions.TestFailedException(reporter.lastErrors.mkString("\n"), err, 5))
      }
    }
  }
}
