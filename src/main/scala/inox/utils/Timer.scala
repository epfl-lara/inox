/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package utils

import scala.language.dynamics
import scala.annotation.switch

import scala.collection.mutable.{ Map => MutableMap, ListBuffer => MutableList }
import scala.util.Try

object DebugSectionTimers extends DebugSection("timers")

private object TimerHelpers {
  sealed abstract class State(private val _next: Option[State]) {
    val next: State = _next getOrElse this
  }
  case object Clean extends State(Some(Running))
  case object Running extends State(Some(Stopped))
  case object Stopped extends State(None)
}

/** A non-reusable timer. */
final class Timer {
  import TimerHelpers._

  private var beg = 0L
  private var end = 0L
  private var state: State = Clean

  def isRunning: Boolean = state == Running
  def isStopped: Boolean = state == Stopped

  def start(): Unit = {
    require(state == Clean)
    beg = System.nanoTime()
    state = state.next
  }

  def stop(): Long = {
    require(state == Running)
    end = System.nanoTime()
    state = state.next
    time
  }

  /** Return the elapsed time in milliseconds. */
  def time: Long = {
    require(state == Stopped)
    (end - beg) / 1000 / 1000
  }
}

/**
 * Provide a `Dynamic`, thread-safe API to measure times.
 *
 * With the exception of [[outputTable]], all methods are thread safe.
 * When calling [[outputTable]], all generated timers MUST have been stopped.
 */
final class TimerStorage private(val _name: Option[String])
  extends Dynamic {

  private val db = MutableMap[String, TimerStorage]()
  private val local = MutableList[Timer]()

  private val name = _name getOrElse ""

  def selectDynamic(name: String): TimerStorage = get(name)

  def get(name: String): TimerStorage = synchronized {
    db.getOrElseUpdate(name, new TimerStorage(Some(name)))
  }

  /**
    * Create a new [[Timer]] associated with this [[TimerStorage]].
    *
    * The callee is required to call [[Timer.stop]] before
    * calling [[Timer.time]].
    */
  def start(): Timer = {
    val t = new Timer
    synchronized { local += t }
    t.start()
    t
  }

  /** Run a timer around a given code, throwing exception. */
  def run[T](body: => T): T = runAndGetTime(body)._2.get

  /** Run a timer around a given code, returning the result and the time it took. */
  def runAndGetTime[T](body: => T): (Long, Try[T]) = {
    val timer = start()
    val res = Try(body)
    val time = timer.stop()
    (time, res)
  }

  /**
   * Output an ASCII table with all (sub-)timers results.
   *
   * NOTE All timers must have been stopped before calling this method.
   */
  def outputTable(printer: String => Unit, asciiOnly: Boolean): Unit = {
    import utils.ASCIIHelpers.{ Cell, Right, Row, Separator, Table }

    var table = Table("Timers")
    table +=
      Row(Seq(
        Cell("name"),
        Cell("min",   align = Right),
        Cell("avg",   align = Right),
        Cell("max",   align = Right),
        Cell("n",     align = Right),
        Cell("total", align = Right)
      ))
    table += Separator

    // stats = (min, avg, max, n, total)
    def stats(s: TimerStorage): (String, String, String, String, String) = (s.local.size: @switch) match {
      case 0 => ("", "", "", "", "")
      case 1 => ("", "", "", "", s.local.head.time.toString)
      case n =>
        val times = s.local map { _.time }
        val total = times.sum
        val avg = total / n
        val min = times.min
        val max = times.max

        (f"$min%d ms", f"$avg%d ms", f"$max%d ms", f"$n%d", f"$total%d ms")
    }

    def rec(indent: String, s: TimerStorage): Unit = {
      // Skip line if no local timer and has no name
      val skip = s.name.isEmpty && s.local.isEmpty
      if (!skip) {
        val localStats = stats(s).productIterator.toSeq map { Cell(_, align = Right) }
        table += Row(Cell(indent + s.name) +: localStats)
      }

      val prevIndent = indent.replace("├", "│").replace("└", " ")

      val subs = s.db.values.toSeq sortBy { _.name }
      val lastIndex = subs.size - 1
      subs.zipWithIndex foreach { case (sub, i) =>
        val nextIndent = if (i == lastIndex) "└ " else "├ "
        rec(prevIndent + nextIndent, sub)
      }
    }

    rec("", this)
    printer(table.render(asciiOnly))
  }
}

object TimerStorage {
  def apply() = new TimerStorage(None)
  def apply(name: String) = new TimerStorage(Some(name))
}

