/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

class TimeoutFor(it: Interruptible) {
  /** Interrupts `it` once `timeout` milliseconds have passed, unless [[finish]] was called
    * before. The check and the interrupt happen under the same lock as [[finish]], so `it`
    * is never interrupted after [[finish]] returned.
    */
  private class Countdown(timeout: Long) extends Thread {
    setDaemon(true)

    private var finished = false

    override def run(): Unit = synchronized {
      val deadline = System.nanoTime + timeout * 1000000L
      var remaining = timeout
      while (!finished && remaining > 0) {
        wait(remaining)
        remaining = (deadline - System.nanoTime + 999999L) / 1000000L
      }
      if (!finished) it.interrupt()
    }

    def finish(): Unit = synchronized {
      finished = true
      notifyAll()
    }
  }

  def interruptAfter[T](timeout: Long)(body: => T): T = {
    val timer = new Countdown(timeout)
    timer.start()
    try body finally timer.finish()
  }
}
