/* Copyright 2009-2021 EPFL, Lausanne */

package inox.utils

import scala.util._
import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import java.util.concurrent.atomic.AtomicInteger

object FutureUtils {

  def findFirst[T](futures: Seq[Future[T]])(cond: T => Boolean): Option[T] = {
    val p = Promise[Option[T]]()
    val n = futures.length
    val i = new AtomicInteger(0)

    for (future <- futures) {
      future.onComplete((result: Try[T]) => result match {
        case Success(res) if cond(res) =>
          p.trySuccess(Some(res))
        case _ =>
          synchronized { i.getAndIncrement() }
          if (i.get == n) p.trySuccess(None)
      })
    }
    Await.result(p.future, Duration.Inf)
  }

}
