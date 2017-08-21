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
  * ''printerOpts'' provides options for tree printers.
  *
  * ''purityOpts'' provides options for assuming checked contracts.
  *
  * ''simpOpts'' provides options for allowing expression simplifications.
  */
trait Program { self =>
  val trees: Trees
  implicit val symbols: trees.Symbols

  implicit def implicitProgram: this.type = this
  implicit def printerOpts(implicit ctx: Context): trees.PrinterOptions = trees.PrinterOptions.fromSymbols(symbols, ctx)
  implicit def purityOpts(implicit ctx: Context): solvers.PurityOptions = solvers.PurityOptions(ctx)
  implicit def simpOpts(implicit ctx: Context): solvers.SimplificationOptions = solvers.SimplificationOptions(ctx)

  type Model = inox.Model {
    val program: self.type
  }

  type Semantics = inox.Semantics {
    val trees: self.trees.type
    val symbols: self.symbols.type
    val program: self.type
  }

  private type Provider = inox.SemanticsProvider {
    val trees: self.trees.type
  }

  private[this] var _semantics: Semantics = null
  implicit def getSemantics(implicit ev: Provider): Semantics = {
    if (_semantics == null) {
      // @nv: tell the type system what's what!
      _semantics = ev.getSemantics(this.asInstanceOf[Program { val trees: self.trees.type }]).asInstanceOf[Semantics]
    }
    _semantics
  }


  def getSolver(implicit ev: Provider, ctx: Context): solvers.SolverFactory {
    val program: self.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.type }
  } = getSemantics.getSolver

  def getSolver(ctx: Context)(implicit ev: Provider): solvers.SolverFactory {
    val program: self.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.type }
  } = getSemantics.getSolver(ctx)

  def getEvaluator(implicit ev: Provider, ctx: Context): evaluators.DeterministicEvaluator {
    val program: self.type
  } = getSemantics.getEvaluator

  def getEvaluator(ctx: Context)(implicit ev: Provider): evaluators.DeterministicEvaluator {
    val program: self.type
  } = getSemantics.getEvaluator(ctx)


  def transform(t: TreeTransformer { val s: self.trees.type }): Program { val trees: t.t.type } = new Program {
    val trees: t.t.type = t.t
    val symbols = self.symbols.transform(t)
  }

  def transform(t: SymbolTransformer { val s: self.trees.type }): Program { val trees: t.t.type } = new Program {
    val trees: t.t.type = t.t
    val symbols = t.transform(self.symbols)
  }

  def withFunctions(functions: Seq[trees.FunDef]): Program { val trees: self.trees.type } = new Program {
    val trees: self.trees.type = self.trees
    val symbols = self.symbols.withFunctions(functions)
  }

  def withADTs(adts: Seq[trees.ADTDefinition]): Program { val trees: self.trees.type } = new Program {
    val trees: self.trees.type = self.trees
    val symbols = self.symbols.withADTs(adts)
  }

  def asString(implicit ctx: Context): String = trees.asString(symbols)
  override def toString: String = asString(Context.empty)
}
