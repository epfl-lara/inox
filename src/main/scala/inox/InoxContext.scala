/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import inox.utils._

import scala.reflect.ClassTag

/** Everything that is part of a compilation unit, except the actual program tree.
  * Contexts are immutable, and so should all their fields (with the possible
  * exception of the reporter).
  */
case class InoxContext(
  reporter: Reporter,
  interruptManager: InterruptManager,
  options: Seq[InoxOption[Any]] = Seq(),
  timers: TimerStorage = new TimerStorage) {

  def findOption[A: ClassTag](optDef: InoxOptionDef[A]): Option[A] = options.collectFirst {
    case InoxOption(`optDef`, value:A) => value
  }

  def findOptionOrDefault[A: ClassTag](optDef: InoxOptionDef[A]): A =
    findOption(optDef).getOrElse(optDef.default)
}

object InoxContext {
  def empty = {
    val reporter = new DefaultReporter(Set())
    InoxContext(reporter, new InterruptManager(reporter))
  }

  def printNames = {
    val reporter = new DefaultReporter(Set())
    InoxContext(
      reporter,
      new InterruptManager(reporter),
      options = Seq(InoxOption[Set[DebugSection]](InoxOptions.optDebug)(Set(ast.DebugSectionTrees)))
    )
  }
}
