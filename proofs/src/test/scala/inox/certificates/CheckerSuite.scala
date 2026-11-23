/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package certificates

import java.nio.file.{Files, Paths}
import scala.jdk.CollectionConverters._

import org.scalatest.funsuite.AnyFunSuite

/** The certificate checker, on a certificate written by hand and on those that Inox prints for
  * the corpus (`proofs/certificates/corpus.txt`). */
class CheckerSuite extends AnyFunSuite {
  import Checker._

  // A template with the parameters `s` and `p` and its own symbol `c`, instantiated once under
  // the root blocker, a definition, an implication between blockers and an assumption.
  val certificate: String =
    """(inox-certificate 2
      |(script
      |(declare-const start Bool)
      |(declare-const b Bool)
      |(declare-const d Bool)
      |(declare-const x Int)
      |(assert start)
      |(assert (=> start (= b (> x 0))))
      |(assert (=> start b))
      |(assert (= d (not b)))
      |(assert (=> start d))
      |(assert (<= x 0))
      |(check-sat)
      |)
      |(templates
      |(script
      |(declare-const s Bool)
      |(declare-const c Bool)
      |(declare-const p Int)
      |(assert (=> s (= c (> p 0))))
      |(assert (=> s c))
      |)
      |(0 (params s p) (expression (> p 0)) 0 1)
      |)
      |(rules
      |(Root (args (start start)) 0)
      |(Instance (args (expression)) (instance 0 ((s start) (p x) (c b))) 1 2)
      |(Define (args (literal d) (value (not b))) 3)
      |(Enables (args (blocker start) (target d)) 4)
      |)
      |(assumptions (query 5) (complete))
      |(solver-symbols
      |(x variable "x$1" "BigInt")
      |)
      |(source-symbols
      |(p variable "p$2" "BigInt")
      |)
      |(cpc
      |(assume @p1 start)
      |(define @t1 () (> x 0))
      |(assume @p2 (=> start (= b @t1)))
      |(step @p3 false :rule resolution :premises (@p1 @p2))
      |))""".stripMargin

  def checked(text: String): Checked = check(certificates(text).head)

  def refused(text: String): String = intercept[Failure](checked(text)).getMessage

  /** The certificate with `from`, which it has once, replaced by `to`. */
  def changed(from: String, to: String): String = {
    assert(certificate.indexOf(from) >= 0 && certificate.indexOf(from) == certificate.lastIndexOf(from), from)
    certificate.replace(from, to)
  }

  test("A certificate whose rules account for its script holds") {
    assert(checked(certificate) == Checked(6, 4, 1, 1, certificates(certificate).head match {
      case SList(items) => items.last match { case SList(_ :: cpc) => cpc; case _ => Nil }
      case _ => Nil
    }))
  }

  test("A template may come without its source") {
    assert(checked(changed(" (expression (> p 0))", "")) == checked(certificate))
  }

  test("Certificates are found among the other lines that Inox prints") {
    val text = "unsat\n" + certificate + "\nWarning: a | b (\nunsat\n(error \"no proof\")\n" + certificate + "\n"
    assert(certificates(text).size == 2)
    assert(certificates("unsat\n(error \"no proof\")\n").isEmpty)
  }

  test("A certificate of another version is refused") {
    assert(refused(changed("(inox-certificate 2", "(inox-certificate 3")).contains("version 3"))
  }

  test("An assert that no rule names is refused") {
    assert(refused(changed("(Enables (args (blocker start) (target d)) 4)\n", "")).contains("assert 4"))
  }

  test("A clause that its rule doesn't build is refused") {
    assert(refused(changed("(assert (=> start d))", "(assert (=> d start))")).contains("is not a clause of the Enables rule"))
    assert(refused(changed("(Define (args (literal d) (value (not b))) 3)", "(Define (args (literal d) (value b)) 3)"))
      .contains("is not a clause of the Define rule"))
    assert(refused(changed("(Root (args (start start)) 0)", "(Root (args (start b)) 0)")).contains("is not a clause of the Root rule"))
  }

  test("A clause is compared up to the simplifications of its connectives") {
    checked(changed("(assert (=> start d))", "(assert (or d (not start)))"))
    checked(changed("(assert (=> start d))", "(assert (=> (and true start) (not (not d))))"))
  }

  test("A rule with an argument that its kind doesn't have, or without one that it has, is refused") {
    assert(refused(changed("(args (blocker start) (target d))", "(args (blocker start) (target d) (guard b))")).contains("no argument guard"))
    assert(refused(changed("(args (blocker start) (target d))", "(args (blocker start))")).contains("no argument target"))
    assert(refused(changed("(Enables (args", "(Implies (args")).contains("not a kind of rule"))
  }

  test("An assert that is not a clause of its template's instance is refused") {
    assert(refused(changed("((s start) (p x) (c b))", "((s start) (p x) (c d))")).contains("is not a clause of the instance"))
    assert(refused(changed("(assert (=> start b))", "(assert (=> start (not b)))")).contains("is not a clause of the instance"))
    assert(refused(changed("((s start) (p x) (c b))", "((p x) (s start) (c b))")).contains("parameters first"))
    assert(refused(changed("((s start) (p x) (c b))", "((s start) (p x) (c (not b)))")).contains("not both symbols"))
  }

  test("A symbol that two rules introduce is refused") {
    val twice = changed("(Enables (args (blocker start) (target d)) 4)", "(Define (args (literal d) (value (not b))) 3)\n(Enables (args (blocker start) (target d)) 4)")
    assert(refused(twice).contains("introduced by both"))
    assert(refused(changed("(Define (args (literal d) (value (not b))) 3)", "(Define (args (literal start) (value start)) 3)"))
      .contains("is not a clause"))
  }

  test("An assumption that is also a clause, or that isn't a literal when it states completeness, is refused") {
    assert(refused(changed("(assumptions (query 5) (complete))", "(assumptions (query 4 5) (complete))")).contains("both an assumption"))
    assert(refused(changed("(assumptions (query 5) (complete))", "(assumptions (query) (complete 5))")).contains("is complete"))
  }

  test("A proof that assumes what the script doesn't assert is refused") {
    assert(refused(changed("(assume @p1 start)", "(assume @p1 (not start))")).contains("the proof assumes (not start)"))
    assert(refused(changed("(define @t1 () (> x 0))", "(define @t1 () (> x 1))")).contains("the proof assumes"))
  }

  /** Inox's command line, which exits by throwing. */
  private class Exit extends Exception
  private class Main extends InoxMain {
    override def exit(error: Boolean) = throw new Exit
  }

  /** What Inox prints for `file` with a `get-proof` after each `check-sat`. */
  def answers(file: String): String = {
    val source = Paths.get("..", file)
    val dir = Files.createTempDirectory("inox-certificates")
    val input = dir.resolve(source.getFileName)
    try {
      Files.writeString(input, Files.readString(source).replace("(check-sat)", "(check-sat)\n(get-proof)"))
      val out = new java.io.ByteArrayOutputStream
      Console.withOut(out)(intercept[Exit](new Main().run(Array("--solvers=smt-cvc5", "--timeout=60", "--model-format=smtlib", input.toString))))
      out.toString("UTF-8")
    } finally {
      Files.deleteIfExists(input)
      Files.deleteIfExists(dir)
    }
  }

  val corpus: Seq[String] = Files.readAllLines(Paths.get("certificates", "corpus.txt")).asScala.toSeq
    .map(_.trim).filter(line => line.nonEmpty && !line.startsWith("#"))

  // the CPC proofs of the corpus are written there, for a CPC checker (see `check.sh`)
  val cpcDir: Option[java.nio.file.Path] = sys.env.get("INOX_CPC_DIR").map(Paths.get(_))

  for (file <- corpus) test(s"The certificates of $file hold") {
    assume(solvers.SolverFactory.hasCVC5, "needs cvc5")
    val text = answers(file)
    // certificates need cvc5 1.4 or later, which cvc5 says when it is older
    assume(!text.contains("(error \"certificates need cvc5"), text.linesIterator.find(_.startsWith("(error")).getOrElse(""))
    val found = certificates(text)
    assert(found.nonEmpty, s"Inox printed no certificate:\n${text.take(2000)}")
    assert(found.size == text.linesIterator.count(_ == "unsat"), "an unsat answer has no certificate")
    for ((certificate, n) <- found.zipWithIndex) {
      val checked = check(certificate)
      for (dir <- cpcDir) {
        Files.createDirectories(dir)
        val name = file.replace('/', '_') + s".${n + 1}.cpc"
        Files.writeString(dir.resolve(name), checked.cpc.map(_.toString + "\n").mkString)
      }
    }
  }
}
