/* Copyright 2009-2016 EPFL, Lausanne */

package inox

import ast._

/** Contains all definitions required to construct a complete Inox program.
  *
  * The elements of this class are typed dependently on the type of ''trees'',
  * which is an object containing classes for expressions, types and definitions
  * used by this program.
  *
  * ''symbols'' contains the actual definitions (classes and functions) of the program.
  *
  * ''ctx'' provides configuration options.
  *
  * ''printerOpts'' provides options for tree printers.
  */
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
