/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package datagen

import utils._

import java.util.concurrent.atomic.AtomicBoolean

object DebugSectionDataGen extends DebugSection("datagen")

trait DataGenerator extends Interruptible {
  val program: Program
  import program.trees._

  implicit val debugSection = DebugSectionDataGen

  def generateFor(ins: Seq[ValDef], satisfying: Expr, maxValid: Int, maxEnumerated: Int): Iterator[Seq[Expr]]

  protected val interrupted: AtomicBoolean = new AtomicBoolean(false)

  def interrupt(): Unit = {
    interrupted.set(true)
  }

  def recoverInterrupt(): Unit = {
    interrupted.set(false)
  }
}
