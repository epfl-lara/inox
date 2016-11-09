/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package tip

import utils._
import solvers._

trait TipDebugger extends Solver {
  import program._

  implicit val debugSection: DebugSection

  abstract override def free(): Unit = {
    super.free()
    debugOut.foreach(_.close())
  }

  protected lazy val debugOut: Option[java.io.FileWriter] = {
    if (ctx.reporter.isDebugEnabled) {
      val file = ctx.options.findOptionOrDefault(Main.optFiles).headOption.map(_.getName).getOrElse("NA")
      val n = DebugFileNumbers.next(file)
      val fileName = s"tip-sessions/$file-$n.tip"

      val javaFile = new java.io.File(fileName)
      javaFile.getParentFile.mkdirs()

      ctx.reporter.debug(s"Outputting tip session into $fileName")
      val fw = new java.io.FileWriter(javaFile, false)
      Some(fw)
    } else {
      None
    }
  }
}

// Unique numbers
private[tip] object DebugFileNumbers extends UniqueCounter[String]
