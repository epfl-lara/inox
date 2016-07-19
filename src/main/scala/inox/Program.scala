/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import ast._

trait Program {
  val trees: Trees
  implicit val symbols: trees.Symbols
  implicit val ctx: InoxContext

  implicit def implicitProgram: this.type = this
  implicit def printerOpts: trees.PrinterOptions = trees.PrinterOptions.fromSymbols(symbols, ctx)
}
