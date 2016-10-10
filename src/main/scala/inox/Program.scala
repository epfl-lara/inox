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
  implicit val ctx: Context

  implicit def implicitProgram: this.type = this
  implicit def printerOpts: trees.PrinterOptions = trees.PrinterOptions.fromSymbols(symbols, ctx)

  def transform(t: trees.SelfTransformer): Program { val trees: Program.this.trees.type } = new Program {
    val trees: Program.this.trees.type = Program.this.trees
    val symbols = Program.this.symbols.transform(t)
    val ctx = Program.this.ctx
  }

  def transform(t: SymbolTransformer {
    val transformer: TreeTransformer { val s: trees.type }
  }): Program { val trees: t.t.type } = new Program {
    val trees: t.t.type = t.t
    val symbols = t.transform(Program.this.symbols)
    val ctx = Program.this.ctx
  }

  def withFunctions(functions: Seq[trees.FunDef]): Program { val trees: Program.this.trees.type } = new Program {
    val trees: Program.this.trees.type = Program.this.trees
    val symbols = Program.this.symbols.withFunctions(functions)
    val ctx = Program.this.ctx
  }

  def withADTs(adts: Seq[trees.ADTDefinition]): Program { val trees: Program.this.trees.type } = new Program {
    val trees: Program.this.trees.type = Program.this.trees
    val symbols = Program.this.symbols.withADTs(adts)
    val ctx = Program.this.ctx
  }
}
