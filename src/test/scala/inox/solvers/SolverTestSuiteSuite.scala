/* Copyright 2009-2026 EPFL, Lausanne */

package inox
package solvers

import org.scalatest.funsuite.AnyFunSuite

/** Checks the configuration of the solver suites themselves. */
class SolverTestSuiteSuite extends AnyFunSuite {

  /** One instance of each solver suite of this package, found on the classpath so that a new
    * suite is checked without being listed here. */
  private lazy val suites: Seq[SolverTestSuite] = {
    val base = classOf[SolverTestSuite]
    val dir = new java.io.File(base.getProtectionDomain.getCodeSource.getLocation.toURI)
    val pkg = new java.io.File(dir, base.getPackageName.replace('.', '/'))
    val classes = Option(pkg.listFiles).toSeq.flatten
      .map(_.getName)
      .filter(n => n.endsWith(".class") && !n.contains("$"))
      .map(n => Class.forName(s"${base.getPackageName}.${n.stripSuffix(".class")}"))
      .filter(c => base.isAssignableFrom(c) && !java.lang.reflect.Modifier.isAbstract(c.getModifiers))
    classes.map(_.getDeclaredConstructor().newInstance().asInstanceOf[SolverTestSuite])
  }

  test("Solver suites are found") {
    assert(suites.exists(_.isInstanceOf[ArithmeticSemanticsSuite]))
    assert(suites.exists(_.isInstanceOf[PartialOperationSemanticsSuite]))
  }

  test("Known issues and ground-only tests name existing tests") {
    // `<name> solver=<solver>`, followed by the reason it is ignored or only checks ground expressions
    val TestName = """(.*) solver=([^ ]+).*""".r
    val registered: Set[(String, String)] = suites.flatMap(_.testNames).collect {
      case TestName(name, solver) => (name, solver)
    }.toSet

    for (info <- SolverTestSuite.solvers; name <- info.knownIssues.keySet ++ info.groundOnly.keySet) {
      assert(registered((name, info.name)),
        s"${info.name} lists a known issue or ground-only test '$name', but no solver suite runs a test of that name on it")
    }
  }

  test("Every expression is used by a solver suite") {
    // The unrolling suites only run on one solver, so each expression that the solvers encode
    // must be checked by the solver suites, which run on every solver (see `UnrollingTestSuite`).
    // This only checks that each expression shows up in some solver suite's source, which is a
    // tripwire for new expressions and for operations that no solver suite covers at all.
    val sources = new java.io.File("src/test/scala/inox/solvers")
    val expressions = new java.io.File("src/main/scala/inox/ast/Expressions.scala")
    assume(sources.isDirectory && expressions.isFile, "the sources are not available")

    def read(f: java.io.File): String = scala.io.Source.fromFile(f, "UTF-8").mkString
    val CaseClass = """(?m)^\s+sealed case class (\w+)""".r
    val names = CaseClass.findAllMatchIn(read(expressions)).map(_.group(1)).toSet
    assert(names.size > 50, s"only found ${names.size} expressions")

    val suiteNames = suites.map(_.getClass.getSimpleName).toSet
    val suiteSources = Option(sources.listFiles).toSeq.flatten
      .filter(f => suiteNames(f.getName.stripSuffix(".scala")))
      .map(read).mkString("\n")

    // expressions that the solver suites build through other names
    val builtThrough = Map(
      "FPLiteral" -> "Float32Literal", // and Float64Literal
    )

    val unused = names.filterNot { name =>
      val used = builtThrough.getOrElse(name, name)
      s"\\b$used\\b".r.findFirstIn(suiteSources).isDefined
    }
    assert(unused.isEmpty, s"no solver suite uses ${unused.toSeq.sorted.mkString(", ")}")
  }
}
