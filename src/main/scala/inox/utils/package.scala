/* Copyright 2009-2021 EPFL, Lausanne */

package inox

import scala.util._
import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

/** Various utilities used throughout the Inox system */
package object utils {

  /** compute the fixpoint of a function.
    *
    * Apply the input function on an expression as long as until 
    * it stays the same (value equality) or until a set limit.
    *
    * @param f the function for which we search a fixpoint
    * @param limit the maximum number of iteration. Use a negative number for infinity
    * @param e the starting expression on which to apply
    * @return the first value x = f(f(f(...f(e)))) such that `f(x) == x`
    */
  def fixpoint[T](f: T => T, limit: Int = -1)(e: T): T = {
    var v1 = e
    var v2 = f(v1)
    var lim = limit
    while(v2 != v1 && lim != 0) {
      v1 = v2
      lim -= 1
      v2 = f(v2)
    }
    v2
  }

  def findFirst[T](futures: Seq[Future[T]])(cond: T => Boolean): Option[T] = {
    val p = Promise[Option[T]]()
    val n = futures.length
    var i = 0

    for (future <- futures) {
      future.onComplete((result: Try[T]) => result match {
        case Success(res) if cond(res) =>
          p.trySuccess(Some(res))
        case _ =>
          synchronized { i += 1 }
          if (i == n) p.trySuccess(None)
      })
    }
    Await.result(p.future, Duration.Inf)
  }

}
