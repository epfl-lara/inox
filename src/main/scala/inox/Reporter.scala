/* Copyright 2009-2018 EPFL, Lausanne */

package inox

import utils._
import Position.smartPos

abstract class DebugSection(val name: String)

abstract class Reporter(val debugSections: Set[DebugSection]) {

  abstract class Severity
  case object INFO    extends Severity
  case object WARNING extends Severity
  case object ERROR   extends Severity
  case object FATAL   extends Severity
  case object INTERNAL extends Severity
  case class  DEBUG(section: DebugSection) extends Severity

  case class Message(severity: Severity, position: Position, msg: Any)
  // The tag allows to differentiate between different kinds of progress message
  // that should not be collapsed if they are printed one after the other.
  case class ProgressMessage(severity: INFO.type | DEBUG, tag: Any, msg: Any)

  private var _errorCount : Int = 0
  private var _warningCount : Int = 0
  private var _fatalCount : Int = 0

  final def errorCount : Int = _errorCount
  final def warningCount : Int = _warningCount
  final def fatalCount : Int = _fatalCount

  def account(msg: Message): Message = {
    msg.severity match {
      case WARNING                  => _warningCount += 1
      case ERROR                    => _errorCount += 1
      case FATAL | INTERNAL         => _fatalCount += 1
      case _                        =>
    }

    msg
  }

  def emit(msg: Message): Unit
  def emit(msg: ProgressMessage): Unit

  def onFatal(msg: String = ""): Nothing = throw FatalError(msg)

  final def info(pos: Position, msg: Any): Unit    = emit(account(Message(INFO, pos, msg)))
  final def warning(pos: Position, msg: Any): Unit = emit(account(Message(WARNING, pos, msg)))
  final def error(pos: Position, msg: Any): Unit   = emit(account(Message(ERROR, pos, msg)))
  final def title(pos: Position, msg: Any): Unit   = emit(account(Message(INFO, pos, Console.BOLD + msg + Console.RESET)))

  final def fatalError(pos: Position, msg: Any): Nothing = {
    emit(account(Message(FATAL, pos, msg)))
    onFatal(msg.toString)
  }

  final def internalError(pos: Position, msg: Any) : Nothing = {
    emit(account(Message(INTERNAL, pos, msg.toString +
      "\nPlease inform the authors of Inox about this message"
    )))
    onFatal(msg.toString)
  }

  final def internalAssertion(cond : Boolean, pos: Position, msg : Any) : Unit = {
    if (!cond) internalError(pos,msg)
  }

  def reset() = {
    _errorCount = 0
    _warningCount = 0
    _fatalCount = 0
  }

  def terminateIfFatal() = {
    if (fatalCount > 0) {
      try { fatalError("There were fatal errors.") }
      finally { reset() }
    }
  }

  def terminateIfError() = {
    if (errorCount > 0 || fatalCount > 0) {
      try { fatalError("There were errors.") }
      finally { reset() }
    }
  }

  def isDebugEnabled(using section: DebugSection): Boolean = debugSections(section)

  def ifDebug(pos: Position, body: (Any => Unit) => Any)(using section: DebugSection) = {
    if (isDebugEnabled) {
      body( { (msg: Any) => emit(account(Message(DEBUG(section), pos, msg))) } )
    }
  }

  def whenDebug(pos: Position, section: DebugSection)(body: (Any => Unit) => Any): Unit = {
    if (isDebugEnabled(using section)) {
      body( { (msg: Any) => emit(account(Message(DEBUG(section), pos, msg))) } )
    }
  }

  def debug(pos: Position, msg: => Any)(using DebugSection): Unit =
    ifDebug(pos, debug => debug(msg))

  // No-position alternatives
  final def info(msg: Any): Unit          = info(NoPosition, msg)
  final def warning(msg: Any): Unit       = warning(NoPosition, msg)
  final def error(msg: Any): Unit         = error(NoPosition, msg)
  final def error(e: Throwable): Unit     = logTrace(ERROR, e)
  final def title(msg: Any): Unit         = title(NoPosition, msg)
  final def fatalError(msg: Any): Nothing = fatalError(NoPosition, msg)

  final def internalError(msg: Any): Nothing = internalError(NoPosition, msg)
  final def internalError(e: Throwable): Nothing = {
    logTrace(INTERNAL, e)
    internalError(e.getMessage)
  }

  final def internalAssertion(cond : Boolean, msg: Any) : Unit = internalAssertion(cond,NoPosition, msg)

  final def debug(msg: => Any)(using DebugSection): Unit = debug(NoPosition, msg)
  final def ifDebug(body: (Any => Unit) => Any)(using DebugSection): Unit =
    ifDebug(NoPosition, body)
  final def whenDebug(section: DebugSection)(body: (Any => Unit) => Any): Unit =
    whenDebug(NoPosition, section)(body)

  final def debug(pos: Position, msg: => Any, e: Throwable)(using section: DebugSection): Unit = {
    if (isDebugEnabled) {
      debug(pos, msg)
      logTrace(DEBUG(section), e)
    }
  }

  final def debug(e: Throwable)(using DebugSection): Unit =
    debug(NoPosition, e.getMessage, e)

  private def logTrace(severity: Severity, e: Throwable): Unit = synchronized {
    var indent = 0
    def log(msg: Any) = emit(account(Message(severity, NoPosition, ("  " * indent) + msg)))

    var ex = e
    while (ex != null) {
      val prefix = if (indent == 0) "Error" else "Cause"
      log(s"$prefix: ${ex.getMessage}. Trace:")
      for (frame <- ex.getStackTrace)
        log(s"- $frame")

      indent += 1

      val cause = e.getCause
      ex = if (cause ne ex) cause else null // don't loop forever on the same cause!
    }
  }

}

class DefaultReporter(debugSections: Set[DebugSection]) extends Reporter(debugSections) {
  protected case class ProgressPrinting(tag: Any, maxLength: Int)
  protected var lastProgressPrinting: Option[ProgressPrinting] = None

  protected def severityToPrefix(sev: Severity): String = sev match {
    case ERROR    => "["+Console.RED              +" Error  "+Console.RESET+"]"
    case WARNING  => "["+Console.YELLOW           +"Warning "+Console.RESET+"]"
    case INFO     => "["+Console.BLUE             +"  Info  "+Console.RESET+"]"
    case FATAL    => "["+Console.RED+Console.BOLD +" Fatal  "+Console.RESET+"]"
    case INTERNAL => "["+            Console.BOLD +"Internal"+Console.RESET+"]"
    case DEBUG(_) => "["+Console.MAGENTA          +" Debug  "+Console.RESET+"]"
  }

  override final def emit(msg: Message) = synchronized {
    if (lastProgressPrinting.isDefined) {
      clearProgress()
      lastProgressPrinting = None
    }
    doEmit(msg)
  }

  def doEmit(msg: Message) = {
    println(reline(severityToPrefix(msg.severity), smartPos(msg.position) + msg.msg.toString))
    printLineContent(msg.position, false)
  }

  override final def emit(msg: ProgressMessage) = synchronized {
    val (shouldClear, prevLength) = lastProgressPrinting match {
      case Some(ProgressPrinting(prevTag, prevLength)) =>
        (prevTag != msg.tag, prevLength)
      case None => (false, 0)
    }
    if (shouldClear) {
      clearProgress()
    }
    val emitted = doEmit(msg, prevLength)
    lastProgressPrinting = Some(ProgressPrinting(msg.tag, math.max(prevLength, emitted.length)))
  }

  def clearProgress(): Unit = println()

  def doEmit(msg: ProgressMessage, prevLength: Int): String = {
    val toPrint = "\r" + severityToPrefix(msg.severity) + " " + msg.msg.toString
    val diff = prevLength - toPrint.length
    print(toPrint)
    if (diff > 0) {
      // Clear the remaining characters of the previous message
      print(" " * diff)
    }
    toPrint
  }

  def getLine(pos: Position): Option[String] = {
    val lines =
      if (pos == NoPosition) IndexedSeq.empty
      else {
        val source = scala.io.Source.fromFile(pos.file)
        try {
          source.getLines().toIndexedSeq
        } finally {
          source.close()
        }
      }

    if (lines.size >= pos.line && pos.line > 0) {
      Some(lines(pos.line - 1))
    } else {
      None
    }
  }

  val prefixSize = 11

  val blankPrefix = " " * prefixSize

  def printLineContent(pos: Position, asciiOnly: Boolean): Unit =
    getLineContent(pos, asciiOnly).foreach(println)

  def getLineContent(pos: Position, asciiOnly: Boolean): Option[String] = {
    getLine(pos) match {
      case Some(line) =>
        // Scala positions probably assume 1 tab = 8 spaces, so we replaces tabs
        // for the carret (^) computed below to be aligned
        val replLine = blankPrefix + line.replace("\t", " " * 8) + "\n"
        pos match {
          case rp: RangePosition =>
            val bp = rp.focusBegin
            val ep = rp.focusEnd

            val carret = if (bp.line == ep.line) {
              val width = Math.max(ep.col - bp.col, 1)
              "^" * width
            } else {
              val width = Math.max(line.length + 1 - bp.col, 1)
              ("^" * width) + "..."
            }

            if (asciiOnly)
              Some(replLine + blankPrefix + (" " * (bp.col - 1) + carret))
            else
              Some(replLine + blankPrefix + (" " * (bp.col - 1) + Console.RED + carret + Console.RESET))

          case op: OffsetPosition =>
            if (asciiOnly)
              Some(replLine + blankPrefix + (" " * (op.col - 1) + "^"))
            else
              Some(replLine + blankPrefix + (" " * (op.col - 1) + Console.RED + "^" + Console.RESET))
        }
      case None => None
    }
  }

  protected def reline(pfx: String, msg: String) : String = {
    pfx+" "+msg.replaceAll("\n", s"\n$pfx ")
  }

}

class PlainTextReporter(debugSections: Set[DebugSection]) extends DefaultReporter(debugSections) {
  override protected def severityToPrefix(sev: Severity): String = ""

  protected def severityToString(sev: Severity): String = sev match {
    case ERROR    => "error"
    case WARNING  => "warning"
    case INFO     => "info"
    case FATAL    => "fatal"
    case INTERNAL => "internal"
    case DEBUG(_) => "debug"
  }

  override def doEmit(msg: Message) = {
    if (msg.severity == ERROR || msg.severity == FATAL || msg.severity == INTERNAL)
      println(smartPos(msg.position) + "error: " + msg.msg.toString)
    else if (msg.severity == WARNING)
      println(smartPos(msg.position) + "warning: " + msg.msg.toString)
    else if (msg.severity.isInstanceOf[DEBUG])
      println(smartPos(msg.position) + "debug: " + msg.msg.toString)
    else
      println(smartPos(msg.position) + msg.msg.toString)
    printLineContent(msg.position, true)
  }

  override def doEmit(msg: ProgressMessage, prevLength: Int) = {
    val sev = severityToString(msg.severity)
    val toPrint = "\r" + sev + " " + msg.msg.toString
    val diff = prevLength - toPrint.length
    print(toPrint)
    if (diff > 0) {
      print(" " * diff)
    }
    toPrint
  }
}
