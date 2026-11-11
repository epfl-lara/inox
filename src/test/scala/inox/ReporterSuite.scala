/* Copyright 2009-2026 EPFL, Lausanne */

package inox

import org.scalatest.funsuite.AnyFunSuite

import utils._

import java.io.{ByteArrayOutputStream, File, PrintStream}

class ReporterSuite extends AnyFunSuite {

  object testSection extends DebugSection("test")
  object otherSection extends DebugSection("other")

  /** A reporter that records the messages it emits. */
  class RecordingReporter(sections: Set[DebugSection] = Set()) extends Reporter(sections) {
    val messages = scala.collection.mutable.ListBuffer.empty[Message]
    val progress = scala.collection.mutable.ListBuffer.empty[ProgressMessage]
    def emit(msg: Message): Unit = messages += msg
    def emit(msg: ProgressMessage): Unit = progress += msg
    def texts: Seq[String] = messages.map(_.msg.toString).toSeq
  }

  private def captured(body: => Unit): String = {
    val out = new ByteArrayOutputStream
    Console.withOut(new PrintStream(out, true, "UTF-8"))(body)
    out.toString("UTF-8")
  }

  private def withSource[A](lines: String*)(body: File => A): A = {
    val file = File.createTempFile("source", ".scala")
    try {
      java.nio.file.Files.write(file.toPath, lines.mkString("\n").getBytes("UTF-8"))
      body(file)
    } finally file.delete()
  }

  test("Warnings, errors and fatal errors are counted") {
    val r = new RecordingReporter
    r.info("i")
    r.warning("w")
    r.error("e1")
    r.error(NoPosition, "e2")
    assertThrows[FatalError](r.fatalError("f"))
    assert((r.warningCount, r.errorCount, r.fatalCount) == (1, 2, 1))
    assert(r.texts == Seq("i", "w", "e1", "e2", "f"))
    assert(r.messages.map(_.severity) == Seq(r.INFO, r.WARNING, r.ERROR, r.ERROR, r.FATAL))
    r.reset()
    assert((r.warningCount, r.errorCount, r.fatalCount) == (0, 0, 0))
  }

  test("Fatal and internal errors throw FatalError with the message") {
    val r = new RecordingReporter
    val e = intercept[FatalError](r.fatalError("boom"))
    assert(e.msg == "boom")
    val i = intercept[FatalError](r.internalError("oops"))
    assert(i.msg == "oops")
    assert(r.messages.last.severity == r.INTERNAL)
    assert(r.texts.last.contains("Please inform the authors of Inox"))
    assert(r.fatalCount == 2)
  }

  test("Internal assertions only fail when the condition is false") {
    val r = new RecordingReporter
    r.internalAssertion(true, "fine")
    assert(r.messages.isEmpty)
    assertThrows[FatalError](r.internalAssertion(false, "broken"))
  }

  test("terminateIfError stops after errors and resets the counts") {
    val r = new RecordingReporter
    r.terminateIfError()
    r.warning("only a warning")
    r.terminateIfError()
    r.error("an error")
    assertThrows[FatalError](r.terminateIfError())
    assert(r.errorCount == 0 && r.fatalCount == 0)
  }

  test("terminateIfFatal ignores errors but stops after fatal errors") {
    val r = new RecordingReporter
    r.error("an error")
    r.terminateIfFatal()
    assertThrows[FatalError](r.fatalError("fatal"))
    assertThrows[FatalError](r.terminateIfFatal())
    assert(r.fatalCount == 0)
  }

  test("Debug messages are only emitted for enabled sections") {
    val r = new RecordingReporter(Set(testSection))

    {
      given DebugSection = testSection
      assert(r.isDebugEnabled)
      r.debug("shown")
      r.ifDebug(debug => debug("shown too"))
    }
    {
      given DebugSection = otherSection
      assert(!r.isDebugEnabled)
      r.debug("hidden")
      r.ifDebug(debug => debug("hidden too"))
    }
    r.whenDebug(testSection)(debug => debug("when shown"))
    r.whenDebug(otherSection)(debug => debug("when hidden"))

    assert(r.texts == Seq("shown", "shown too", "when shown"))
    assert(r.messages.forall(_.severity == r.DEBUG(testSection)))
  }

  test("Debug messages are not evaluated when their section is disabled") {
    val r = new RecordingReporter
    given DebugSection = testSection
    var evaluated = false
    r.debug { evaluated = true; "msg" }
    assert(!evaluated)
  }

  test("Exceptions are logged with their stack trace and every cause") {
    val r = new RecordingReporter
    val root = new RuntimeException("root")
    val middle = new RuntimeException("middle", root)
    val top = new RuntimeException("top", middle)
    r.error(top)
    val headers = r.texts.filter(_.trim.matches("(Error|Cause): .*"))
    assert(headers.map(_.trim) == Seq("Error: top. Trace:", "Cause: middle. Trace:", "Cause: root. Trace:"))
    // causes are indented by nesting depth
    assert(headers(1).startsWith("  Cause") && headers(2).startsWith("    Cause"))
    assert(r.texts.exists(_.trim.startsWith("- ")), "stack frames missing")
    assert(r.errorCount == r.messages.size)
  }

  test("Logging an exception whose cause is itself terminates") {
    val r = new RecordingReporter
    val e = new Exception("self") {
      override def getCause: Throwable = this
    }
    r.error(e)
    assert(r.texts.count(_.contains("self. Trace:")) == 1)
  }

  test("internalError(Throwable) logs the trace and throws") {
    val r = new RecordingReporter
    assertThrows[FatalError](r.internalError(new RuntimeException("bad")))
    assert(r.texts.head == "Error: bad. Trace:")
  }

  test("debug(Throwable) only logs in enabled sections") {
    val r = new RecordingReporter(Set(testSection))
    locally {
      given DebugSection = otherSection
      r.debug(new RuntimeException("hidden"))
    }
    assert(r.messages.isEmpty)
    locally {
      given DebugSection = testSection
      r.debug(new RuntimeException("shown"))
    }
    assert(r.texts.head == "shown")
    assert(r.texts.exists(_.contains("Error: shown. Trace:")))
  }

  test("The default reporter prefixes messages with their severity") {
    val r = new DefaultReporter(Set())
    val out = captured {
      r.info("an info")
      r.warning("a warning")
      r.error("first line\nsecond line")
    }
    val lines = out.split("\n").map(ReporterSuiteHelpers.plain).toSeq
    assert(lines == Seq(
      "[  Info  ] an info",
      "[Warning ] a warning",
      "[ Error  ] first line",
      "[ Error  ] second line"
    ))
  }

  test("The plain text reporter names the severity in words") {
    val r = new PlainTextReporter(Set())
    val out = captured {
      r.info("an info")
      r.warning("a warning")
      r.error("an error")
      try r.fatalError("a fatal error") catch { case _: FatalError => }
    }
    assert(out.split("\n").toSeq == Seq("an info", "warning: a warning", "error: an error", "error: a fatal error"))
  }

  test("Messages show the source line and a caret under the position") {
    withSource("val x = 1", "  val y = x + 2") { file =>
      val r = new DefaultReporter(Set())
      val pos = OffsetPosition(2, 11, 0, file)
      assert(r.getLine(pos) == Some("  val y = x + 2"))
      assert(r.getLineContent(pos, asciiOnly = true) == Some(
        r.blankPrefix + "  val y = x + 2\n" + r.blankPrefix + " " * 10 + "^"))

      val range = RangePosition(2, 11, 0, 2, 16, 0, file)
      assert(r.getLineContent(range, asciiOnly = true) == Some(
        r.blankPrefix + "  val y = x + 2\n" + r.blankPrefix + " " * 10 + "^^^^^"))

      val multiline = RangePosition(1, 5, 0, 2, 3, 0, file)
      assert(r.getLineContent(multiline, asciiOnly = true).get.endsWith("    ^^^^^..."))

      val colored = r.getLineContent(pos, asciiOnly = false).get
      assert(colored.contains(Console.RED + "^" + Console.RESET))

      val out = captured(r.warning(pos, "careful"))
      val lines = out.split("\n").map(ReporterSuiteHelpers.plain).toSeq
      assert(lines.head.endsWith(":2:11: careful"))
      assert(lines(1) == r.blankPrefix + "  val y = x + 2")
    }
  }

  test("Positions past the end of the file show no source line") {
    withSource("only one line") { file =>
      val r = new DefaultReporter(Set())
      assert(r.getLine(OffsetPosition(5, 1, 0, file)).isEmpty)
      assert(r.getLine(NoPosition).isEmpty)
      assert(r.getLineContent(NoPosition, asciiOnly = true).isEmpty)
    }
  }

  test("Progress messages overwrite each other until the tag changes") {
    val r = new PlainTextReporter(Set())
    val out = captured {
      r.emit(r.ProgressMessage(r.INFO, "a", "a long progress message"))
      r.emit(r.ProgressMessage(r.INFO, "a", "short"))
      r.emit(r.ProgressMessage(r.INFO, "b", "other"))
      r.info("done")
    }
    // Shorter messages are padded to erase longer ones, and a new tag or a message starts a new line.
    assert(out ==
      "\rinfo a long progress message" +
      "\rinfo short" + " " * ("a long progress message".length - "short".length) +
      "\n\rinfo other" + " " * ("a long progress message".length - "other".length) +
      "\ndone\n")
  }

  test("Every severity has a prefix and a name") {
    val r = new DefaultReporter(Set(testSection))
    val out = captured {
      try r.fatalError("fatal") catch { case _: FatalError => }
      try r.internalError("internal") catch { case _: FatalError => }
      r.debug("debugging")(using testSection)
      r.emit(r.ProgressMessage(r.INFO, "a", "a long progress message"))
      r.emit(r.ProgressMessage(r.DEBUG(testSection), "a", "short"))
    }
    val plain = ReporterSuiteHelpers.plain(out)
    assert(plain.contains("[ Fatal  ] fatal"))
    assert(plain.contains("[Internal] internal"))
    assert(plain.contains("[ Debug  ] debugging"))
    assert(plain.contains("\r[  Info  ] a long progress message"))
    assert(plain.contains("\r[ Debug  ] short "))

    class NamingReporter extends PlainTextReporter(Set(testSection)) {
      def name(sev: Severity) = severityToString(sev)
    }
    val p = new NamingReporter
    val pout = captured {
      try p.internalError("internal") catch { case _: FatalError => }
      p.debug("debugging")(using testSection)
      p.emit(p.ProgressMessage(p.DEBUG(testSection), "a", "progress"))
    }
    assert(pout.contains("error: internal"))
    assert(pout.contains("debug: debugging"))
    assert(pout.contains("\rdebug progress"))
    assert(Seq(p.ERROR, p.WARNING, p.INFO, p.FATAL, p.INTERNAL, p.DEBUG(testSection)).map(p.name) ==
      Seq("error", "warning", "info", "fatal", "internal", "debug"))
  }
}

object ReporterSuiteHelpers {
  /** Removes ANSI color codes. */
  def plain(s: String): String = ASCIIHelpers.trimNonPrintable(s)
}
