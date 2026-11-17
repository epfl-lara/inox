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
}
