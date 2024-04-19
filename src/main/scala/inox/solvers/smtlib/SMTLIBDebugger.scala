/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package smtlib

import utils._
import _root_.smtlib.trees.Terms._

case object DebugSectionSMT extends DebugSection("smt")

trait SMTLIBDebugger extends SMTLIBTarget {
  import context.{given, _}
  import program._

  protected def interpreterOpts: Seq[String]

  val debugSection: DebugSection
  given givenSmtlibDebugSection: DebugSection = debugSection

  override def free(): Unit = {
    super.free()
    debugOut.foreach(_.close())
  }
  lazy private val file = options.findOptionOrDefault(Main.optFiles).headOption.map(_.getName).getOrElse("NA")
  lazy private val smtLibFileId: Int = DebugFileNumbers.next(targetName + file)

  /**
   * Returns the SMT-lib file query ID if the debug=smt option is activated, otherwise None
   * @return
   */
  def getSmtLibFileIdIfDebug: Option[Int] = {
    given DebugSectionSMT.type = DebugSectionSMT
    if (reporter.isDebugEnabled) {
      Some(smtLibFileId)
    } else {
      None
    }
  }
  /* Printing VCs */
  protected lazy val debugOut: Option[java.io.FileWriter] = {
    given DebugSectionSMT.type = DebugSectionSMT
    if (reporter.isDebugEnabled) {
      val fileName = s"smt-sessions/$targetName-$file-$smtLibFileId.smt2"

      val javaFile = new java.io.File(fileName)
      javaFile.getParentFile.mkdirs()

      reporter.debug(s"Outputting smt session into $fileName")

      val fw = new java.io.FileWriter(javaFile, false)
      fw.write("; Options: " + interpreterOpts.mkString(" ") + "\n")

      Some(fw)
    } else {
      None
    }
  }

  override def emit(cmd: SExpr, rawOut: Boolean = false): SExpr = {
    debugOut.foreach { o =>
      interpreter.printer.printSExpr(cmd, o)
      o.write("\n")
      o.flush()
    }
    super.emit(cmd, rawOut = rawOut)
  }
}

// Unique numbers
private[smtlib] object DebugFileNumbers extends UniqueCounter[String]
