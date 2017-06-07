/* Copyright 2009-2016 EPFL, Lausanne */

package inox

class TestSilentReporter extends DefaultReporter(Set()) {
  var lastErrors: List[String] = Nil

  override def emit(msg: Message): Unit = msg match { 
    case Message(ERROR, _, msg) => lastErrors ++= List(msg.toString)
    case Message(FATAL, _, msg) => lastErrors ++= List(msg.toString)
    case _ =>
  }

  override def debug(pos: utils.Position, msg: => Any)(implicit section: DebugSection): Unit = {
    //println(msg)
    super.debug(pos, msg)
  }
}

class TestErrorReporter extends DefaultReporter(Set()) {
  override def emit(msg: Message): Unit = msg match { 
    case Message(ERROR | FATAL, _, _) => super.emit(msg)
    case _ =>
  }
}
