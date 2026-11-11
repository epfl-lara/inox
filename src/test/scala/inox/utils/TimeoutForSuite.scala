/* Copyright 2009-2026 EPFL, Lausanne */

package inox.utils

import org.scalatest.funsuite.AnyFunSuite

import java.util.concurrent.atomic.AtomicInteger

class TimeoutForSuite extends AnyFunSuite {

  private class Counter extends Interruptible {
    val interrupts = new AtomicInteger(0)
    def interrupt(): Unit = interrupts.incrementAndGet()
  }

  test("a body that returns in time is never interrupted") {
    val c = new Counter
    assert(new TimeoutFor(c).interruptAfter(100L)(42) == 42)
    Thread.sleep(300L)
    assert(c.interrupts.get == 0)
  }

  test("a body that runs past the timeout is interrupted once") {
    val c = new Counter
    new TimeoutFor(c).interruptAfter(50L) {
      val start = System.currentTimeMillis
      while (c.interrupts.get == 0 && System.currentTimeMillis - start < 10000L) Thread.sleep(5L)
    }
    Thread.sleep(200L)
    assert(c.interrupts.get == 1)
  }

  test("a body that throws is not interrupted afterwards") {
    val c = new Counter
    intercept[IllegalStateException] {
      new TimeoutFor(c).interruptAfter(100L)(throw new IllegalStateException)
    }
    Thread.sleep(300L)
    assert(c.interrupts.get == 0)
  }

  test("the timer doesn't outlive the body") {
    val c = new Counter
    // Timer threads join the group of the thread that starts them, which keeps them apart
    // from the threads of the tests that run in parallel.
    val group = new ThreadGroup("timeout-for-suite")
    val runner = new Thread(group, () => {
      for (_ <- 1 to 20) new TimeoutFor(c).interruptAfter(60000L)(())
    })
    runner.start()
    runner.join()
    val start = System.currentTimeMillis
    while (group.activeCount > 0 && System.currentTimeMillis - start < 5000L) Thread.sleep(10L)
    assert(group.activeCount == 0)
    assert(c.interrupts.get == 0)
  }
}
