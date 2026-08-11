/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import _root_.smtlib.trees.Commands._
import _root_.smtlib.interpreters.ProcessInterpreter

import SolverResponses._

// Princess is a JVM library, not a native binary, so we run it as an external
// process by re-launching it as its own JVM speaking incremental SMT-LIB2 over
// stdin/stdout (`+stdin +incremental`), exactly like the Z3/CVC5 binaries do.
// Princess doesn't print "success" after commands by default, so we turn that
// on explicitly, mirroring what CVC5Interpreter does.
class PrincessInterpreter(executable: String, args: Array[String])
  extends ProcessInterpreter(executable, args) {

  printer.printCommand(SetOption(PrintSuccess(true)), in)
  in.write("\n")
  in.flush()
  parser.parseGenResponse
}

trait PrincessTarget extends SMTLIBTarget with SMTLIBDebugger {
  import context.{given, _}

  def targetName = "princess"

  // sbt (and other tools) load project classes via custom classloaders without
  // forking, so `java.class.path` alone may omit Princess's jar; walk the
  // classloader chain as well to recover the jars actually in use.
  private def classpath: String = {
    def urls(cl: ClassLoader): Seq[java.net.URL] = cl match {
      case null => Seq.empty
      case u: java.net.URLClassLoader => u.getURLs.toSeq ++ urls(u.getParent)
      case other => urls(other.getParent)
    }
    val fromClassLoader = urls(getClass.getClassLoader).map(_.getFile)
    val fromProperty = Option(System.getProperty("java.class.path")).toSeq
      .flatMap(_.split(java.io.File.pathSeparator))
    (fromClassLoader ++ fromProperty).distinct.mkString(java.io.File.pathSeparator)
  }

  protected def interpreterOpts = Seq(
    "-cp", classpath,
    "ap.CmdlMain", "+quiet", "+stdin", "+incremental"
  )

  protected val interpreter: ProcessInterpreter = {
    val opts = interpreterOpts
    reporter.debug("Invoking solver "+targetName+" with "+opts.mkString(" "))
    new PrincessInterpreter(System.getProperty("java.home") + "/bin/java", opts.toArray)
  }
}

trait PrincessSMTLIBSolver extends SMTLIBSolver with PrincessTarget {
  import program.trees._

  // Princess's SMT-LIB2 frontend doesn't implement `check-sat-assuming`, which
  // AbstractUnrollingSolver relies on for every incremental check. Simulate it
  // with push/assert/check-sat/pop, which Princess's frontend does support.
  override def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
    push()
    try {
      assumptions.foreach(assertCnstr)
      extractResponse(config, emit(CheckSat()), assumptions)
    } finally {
      pop()
    }
  }
}
