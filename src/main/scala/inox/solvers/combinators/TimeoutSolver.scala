/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package combinators

import utils._
import scala.concurrent.duration._

trait TimeoutSolver extends Solver {
  import program.trees._
  import SolverResponses._

  val ti = new TimeoutFor(this)

  var optTimeout: Option[Long] = None

  def setTimeout(timeout: Long): this.type = {
    optTimeout = Some(timeout)
    this
  }

  def setTimeout(timeout: Duration): this.type = {
    optTimeout = Some(timeout.toMillis)
    this
  }

  abstract override def check(config: CheckConfiguration) = {
    optTimeout match {
      case Some(to) =>
        ti.interruptAfter(to) {
          super.check(config)
        }
      case None =>
        super.check(config)
    }
  }

  abstract override def checkAssumptions(config: Configuration)
                                        (assumptions: Set[Expr]) = {
    optTimeout match {
      case Some(to) =>
        ti.interruptAfter(to) {
          super.checkAssumptions(config)(assumptions)
        }
      case None =>
        super.checkAssumptions(config)(assumptions)
    }
  }

}
