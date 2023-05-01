/* Copyright 2009-2018 EPFL, Lausanne */

package inox

import inox.utils.Position.smartPos

class TestSilentReporter extends DefaultReporter(Set()) {
  var lastErrors: List[String] = Nil

  override def clearProgress(): Unit = ()

  override def doEmit(msg: Message): Unit = msg match {
    case Message(ERROR, pos, msg) => lastErrors ++= List(smartPos(pos) + msg.toString)
    case Message(FATAL, pos, msg) => lastErrors ++= List(smartPos(pos) + msg.toString)
    case _ =>
  }

  override def debug(pos: utils.Position, msg: => Any)(using DebugSection): Unit = {
    //println(msg)
    super.debug(pos, msg)
  }

  override def doEmit(msg: ProgressMessage, prevLength: Int): String = msg.msg.toString
}

class TestErrorReporter extends DefaultReporter(Set()) {
  override def clearProgress(): Unit = ()

  override def doEmit(msg: Message): Unit = msg match {
    case Message(ERROR | FATAL, _, _) => super.doEmit(msg)
    case _ =>
  }

  override def doEmit(msg: ProgressMessage, prevLength: Int): String = msg.msg.toString
}
