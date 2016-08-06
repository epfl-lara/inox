/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import ast._

trait Program {
  val trees: Trees
  implicit val symbols: trees.Symbols
  implicit val ctx: InoxContext

  implicit def implicitProgram: this.type = this
  implicit def printerOpts: trees.PrinterOptions = trees.PrinterOptions.fromSymbols(symbols, ctx)

  def transform(t: trees.TreeTransformer): Program { val trees: Program.this.trees.type } = new Program {
    val trees: Program.this.trees.type = Program.this.trees
    val symbols = Program.this.symbols.transform(t)
    val ctx = Program.this.ctx
  }

  def extend(functions: Seq[trees.FunDef] = Seq.empty, classes: Seq[trees.ClassDef] = Seq.empty):
            Program { val trees: Program.this.trees.type } = new Program {
    val trees: Program.this.trees.type = Program.this.trees
    val symbols = Program.this.symbols.extend(functions, classes)
    val ctx = Program.this.ctx
  }
}
