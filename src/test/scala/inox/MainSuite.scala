/* Copyright 2009-2026 EPFL, Lausanne */

package inox

import org.scalatest.funsuite.AnyFunSuite

import java.io.{File, FileOutputStream}
import java.nio.file.Files

/** Runs the Inox command line on small TIP and binary files. */
class MainSuite extends AnyFunSuite {

  case class Exit(error: Boolean) extends Exception(s"exit(error = $error)")

  /** A command line that records its messages and throws on exit. */
  class TestMain extends InoxMain {
    val messages = scala.collection.mutable.ListBuffer.empty[String]

    override protected def newReporter(debugSections: Set[DebugSection]): Reporter =
      new DefaultReporter(debugSections) {
        override def doEmit(msg: Message): Unit =
          messages += utils.ASCIIHelpers.trimNonPrintable(msg.msg.toString)
        override def doEmit(msg: ProgressMessage, prevLength: Int): String = ""
        override def clearProgress(): Unit = ()
      }

    override def exit(error: Boolean) = throw Exit(error)

    /** Runs the command line and returns whether it exited with an error. */
    def exitCode(args: String*): Boolean = intercept[Exit](run(args.toArray)).error

    def output: String = messages.mkString("\n")
  }

  private def withFiles[A](contents: String*)(body: Seq[String] => A): A = {
    val dir = Files.createTempDirectory("inox-main")
    val files = contents.zipWithIndex.map { case (content, i) =>
      val file = dir.resolve(s"file$i.tip")
      Files.write(file, content.getBytes("UTF-8"))
      file.toString
    }
    try body(files) finally {
      files.foreach(f => Files.deleteIfExists(new File(f).toPath))
      Files.deleteIfExists(dir)
    }
  }

  val sat = "(declare-const x Int)\n(assert (> x 41))\n(assert (< x 43))\n(check-sat)\n"
  val unsat = "(declare-const x Int)\n(assert (< x x))\n(check-sat)\n"
  val groundSat = "(assert (= (+ 1 1) 2))\n(check-sat)\n"
  val groundUnsat = "(assert (= (+ 1 1) 3))\n(check-sat)\n"

  /** The answer to the get-proof of an unsat query with `solvers`. */
  def proofOf(solvers: String): String = withFiles(unsat + "(get-proof)\n") { case Seq(file) =>
    val main = new TestMain
    val out = new java.io.ByteArrayOutputStream
    Console.withOut(out)(assert(!main.exitCode(s"--solvers=$solvers", "--timeout=30", file)))
    assert(main.messages.contains(s"$file => UNSAT"))
    out.toString
  }

  // certificates need cvc5 1.4 or later, which cvc5 says when it is older
  lazy val cvc5Proof: String = {
    assume(solvers.SolverFactory.hasCVC5, "needs cvc5")
    val proof = proofOf("smt-cvc5")
    assume(!proof.startsWith("(error \"certificates need cvc5"), proof)
    proof
  }

  test("get-proof prints the certificate of a proved query") {
    assert(cvc5Proof.startsWith("(inox-certificate 6\n(script\n") && cvc5Proof.contains("\n(cpc\n"), cvc5Proof)
  }

  test("get-proof says why the solver gives no certificate") {
    withFiles(unsat + "(get-proof)\n") { case Seq(file) =>
      val main = new TestMain
      val out = new java.io.ByteArrayOutputStream
      Console.withOut(out)(assert(!main.exitCode("--solvers=princess", "--timeout=30", file)))
      assert(main.messages.contains(s"$file => UNSAT"))
      assert(out.toString == "(error \"the solver does not produce proofs\")\n", out.toString)
    }
  }

  test("get-proof prints the certificate of a portfolio with a solver that proves the query") {
    cvc5Proof
    val proof = proofOf("princess,smt-cvc5")
    assert(proof.startsWith("(inox-certificate 6\n(script\n") && proof.contains("\n(cpc\n"), proof)
  }

  test("Satisfiable files are reported with their model") {
    withFiles(sat) { case Seq(file) =>
      val main = new TestMain
      assert(!main.exitCode("--solvers=princess", file))
      assert(main.messages.contains(s"$file => SAT"))
      assert(main.output.contains("42"), main.output)
    }
  }

  test("Unsatisfiable files are reported as such") {
    withFiles(unsat) { case Seq(file) =>
      val main = new TestMain
      assert(!main.exitCode("--solvers=princess", "--timeout=30", file))
      assert(main.messages.contains(s"$file => UNSAT"))
    }
  }

  test("Unknown results make the command fail") {
    withFiles(sat) { case Seq(file) =>
      val main = new TestMain
      assert(main.exitCode("--solvers=eval", file))
      assert(main.messages.contains(s"$file => UNKNOWN"))
    }
  }

  test("Every file is checked") {
    withFiles(groundSat, groundUnsat) { case Seq(f1, f2) =>
      val main = new TestMain
      assert(!main.exitCode("--solvers=eval", f1, f2))
      assert(main.messages.contains(s"$f1 => SAT"))
      assert(main.messages.contains(s"$f2 => UNSAT"))
    }
  }

  test("The program can be printed") {
    withFiles(groundSat) { case Seq(file) =>
      val main = new TestMain
      assert(!main.exitCode("--solvers=eval", "--print-program", file))
      assert(main.messages.exists(_.startsWith(s"Program in $file")))
    }
  }

  test("A missing input file is an error") {
    val main = new TestMain
    assert(main.exitCode("--solvers=eval"))
    assert(main.output.contains("Input file was not specified"))
  }

  test("Unknown options are errors") {
    val main = new TestMain
    assert(main.exitCode("--no-such-option", "file.tip"))
    assert(main.output.contains("Unknown option: no-such-option"))
  }

  test("Invalid option values are errors") {
    for (arg <- Seq("--timeout=soon", "--solvers=nope", "--debug=nope", "--format=nope")) {
      val main = new TestMain
      assert(main.exitCode(arg, "file.tip"), arg)
      assert(main.output.contains(s"Invalid option usage: $arg"), arg)
    }
  }

  test("Options cannot be given twice") {
    val main = new TestMain
    assert(main.exitCode("--timeout=1", "--timeout=2", "file.tip"))
    assert(main.output.contains("Duplicate option: timeout"))
  }

  test("The help lists every option by category") {
    val main = new TestMain
    assert(!main.exitCode("--help"))
    assert(main.messages.exists(_.startsWith("Usage: inox [OPTION]... FILE...")))
    for (category <- Seq("General", "Solvers", "Evaluators", "Printing"))
      assert(main.messages.contains(category), category)
    for (opt <- main.options.keys)
      assert(main.messages.exists(_.startsWith(opt.usageDesc)), opt.name)
    assert(main.messages.exists(m => m.startsWith("--timeout=t") && m.contains("(default: ")))
  }

  test("Debug sections can be enabled by name or all at once") {
    val main = new TestMain
    import main.optDebug
    given Reporter = new TestSilentReporter
    assert(optDebug.parse("all").value == Set(
      utils.DebugSectionTimers, solvers.DebugSectionSolver, solvers.smtlib.DebugSectionSMT, tip.DebugSectionTip))
    assert(optDebug.parse("timers").value == Set(utils.DebugSectionTimers))
    assert(optDebug.parse("solver,smt").value == Set(solvers.DebugSectionSolver, solvers.smtlib.DebugSectionSMT))
  }

  test("Timers are printed in the timers debug section") {
    withFiles(groundSat) { case Seq(file) =>
      val main = new TestMain
      assert(!main.exitCode("--solvers=eval", "--debug=timers", "--no-colors", file))
      assert(main.messages.exists(_.contains("solvers")), main.output)
    }
  }

  test("The input format accepts tip and binary with an optional method") {
    val main = new TestMain
    import main.{optFormat, Tip, Binary}
    assert(optFormat.parser("tip") == Some(Tip))
    assert(optFormat.parser("TIP") == Some(Tip))
    assert(optFormat.parser("binary") == Some(Binary(None)))
    assert(optFormat.parser("binary:check") == Some(Binary(Some("check"))))
    assert(optFormat.parser("xml").isEmpty)
  }

  test("The options that a script sets apply to the queries after them") {
    // functions can only be compared under the option, and the solver doesn't know SMT-LIB's
    val script = "(set-option :produce-models true)\n(assert (= 1 2))\n(check-sat)\n" +
      "(set-option :function-equality extensional)\n(assert (= (lambda ((x Int)) x) (lambda ((x Int)) (+ x 0))))\n(check-sat)\n"
    withFiles(script) { case Seq(file) =>
      val main = new TestMain
      assert(!main.exitCode("--solvers=princess", "--timeout=30", "--format=smtlib3", file), main.output)
      assert(main.output.split(s"$file => UNSAT", -1).size == 3, main.output)
    }
  }

  test("SMT-LIB 3 inputs are read with --format=smtlib3 or from .smt3 files") {
    val main = new TestMain
    import main.{optFormat, SMTLIB3}
    assert(optFormat.parser("smtlib3") == Some(SMTLIB3))
    assert(optFormat.parser("smt3") == Some(SMTLIB3))

    val script = "(declare-const f (-> (! Int :var n :restrict (> n 0)) Int))\n(assert (= (f 1) 2))\n(check-sat)\n"
    withFiles(script) { case Seq(file) =>
      val main = new TestMain
      assert(!main.exitCode("--solvers=princess", "--format=smtlib3", file))
      assert(main.messages.contains(s"$file => SAT"), main.output)

      val smt3 = file.stripSuffix(".tip") + ".smt3"
      Files.copy(new File(file).toPath, new File(smt3).toPath)
      try {
        val main = new TestMain
        assert(!main.exitCode("--solvers=princess", smt3))
        assert(main.messages.contains(s"$smt3 => SAT"), main.output)
      } finally Files.deleteIfExists(new File(smt3).toPath)
    }
  }

  test("Binary files are solved from the named function's body") {
    import inox.trees._
    import inox.trees.dsl._
    val checkID = FreshIdentifier("check")
    val check = mkFunDef(checkID)() { _ => (Seq(), BooleanType(), { _ => E(BigInt(2)) === E(BigInt(1)) + E(BigInt(1)) }) }
    val symbols = NoSymbols.withFunctions(Seq(check))

    val file = File.createTempFile("symbols", ".inoxser")
    try {
      val serializer = utils.Serializer(inox.trees)
      import serializer.{given, _}
      val out = new FileOutputStream(file)
      try serializer.serialize(symbols, out) finally out.close()

      val main = new TestMain
      assert(!main.exitCode("--solvers=eval", "--format=binary:check", file.getPath))
      assert(main.messages.contains(s"${file.getPath} => SAT"))

      // without a method, the symbols are only loaded
      val load = new TestMain
      assert(!load.exitCode("--solvers=eval", "--format=binary", "--print-program", file.getPath))
      assert(load.output.contains("def check"))
      assert(!load.output.contains("=> SAT"))
    } finally file.delete()
  }

  test("Missing binary files are errors") {
    val main = new TestMain
    assert(main.exitCode("--format=binary", "/no/such/file.inoxser"))
    assert(main.output.contains("Input file was not found"))
  }

  /** Runs the command line and returns whether it failed and what it printed on standard output. */
  private def stdout(main: TestMain, args: String*): (Boolean, String) = {
    val out = new java.io.ByteArrayOutputStream
    val error = Console.withOut(out)(main.exitCode(args*))
    (error, out.toString("UTF-8").trim)
  }

  test("SMT-LIB model format prints sat with a get-value model") {
    withFiles(sat) { case Seq(file) =>
      val (error, out) = stdout(new TestMain, "--solvers=princess", "--model-format=smtlib", file)
      assert(!error)
      assert(out == "sat\n((x 42))")
    }
  }

  test("SMT-LIB model format prints unsat and unknown") {
    withFiles(unsat) { case Seq(file) =>
      val (error, out) = stdout(new TestMain, "--solvers=princess", "--timeout=30", "--model-format=smtlib", file)
      assert(!error)
      assert(out == "unsat")
    }
    withFiles(sat) { case Seq(file) =>
      val (error, out) = stdout(new TestMain, "--solvers=eval", "--model-format=smtlib", file)
      assert(error)
      assert(out == "unknown")
    }
  }
}
