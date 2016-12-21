/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package utils

class TimeoutFor(it: Interruptible) {
  private class Countdown(timeout: Long, onTimeout: => Unit) extends Thread {
    private var keepRunning = true
    override def run() : Unit = {
      val startTime : Long = System.currentTimeMillis
      var exceeded : Boolean = false

      while(!exceeded && keepRunning) {
        if(timeout < (System.currentTimeMillis - startTime)) {
          exceeded = true
        }
        Thread.sleep(10)
      }

      if (exceeded && keepRunning) {
        onTimeout
      }
    }

    def finishedRunning() : Unit = {
      keepRunning = false
    }
  }

  def interruptAfter[T](timeout: Long)(body: => T): T = {
    val timer = new Countdown(timeout, {
      it.interrupt()
    })

    timer.start()
    val res = body
    timer.finishedRunning()

    res
  }
}
