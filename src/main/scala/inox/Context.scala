/* Copyright 2009-2018 EPFL, Lausanne */

package inox

import inox.utils._

/** Everything that is part of a compilation unit, except the actual program tree.
  * Contexts are immutable, and so should all their fields (with the possible
  * exception of the reporter).
  */
case class Context(
  reporter: Reporter,
  interruptManager: InterruptManager,
  options: Options = Options(Seq()),
  timers: TimerStorage = TimerStorage()) {

  given givenContext: this.type = this

  def withOpts(opts: OptionValue[?]*): Context = copy(options = options ++ opts)
}

object Context {
  def empty = {
    val reporter = new DefaultReporter(Set())
    Context(reporter, new InterruptManager(reporter))
  }
}
