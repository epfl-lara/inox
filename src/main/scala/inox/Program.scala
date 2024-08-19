/* Copyright 2009-2018 EPFL, Lausanne */

package inox

import ast._
import transformers._

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
  val symbols: trees.Symbols

  given givenProgram: this.type = this
  implicit def printerOpts(using ctx: Context): trees.PrinterOptions = trees.PrinterOptions.fromSymbols(symbols, ctx)
  implicit def purityOpts(using ctx: Context): solvers.PurityOptions = solvers.PurityOptions(ctx)
  implicit def simpOpts(using ctx: Context): solvers.SimplificationOptions = solvers.SimplificationOptions(ctx)

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

  private var _semantics: Semantics = null
  implicit def getSemantics(using ev: Provider): Semantics = {
    if (_semantics eq null) {
      // @nv: tell the type system what's what!
      _semantics = ev.getSemantics(
        this.asInstanceOf[Program { val trees: self.trees.type }]
      ).asInstanceOf[Semantics]
    }
    _semantics
  }


  def getSolver(using Provider, Context): solvers.SolverFactory {
    val program: self.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.type }
  } = getSemantics.getSolver

  def getSolver(ctx: Context)(using Provider): solvers.SolverFactory {
    val program: self.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.type }
  } = getSemantics.getSolver(using ctx)

  def getEvaluator(using Provider, Context): evaluators.DeterministicEvaluator {
    val program: self.type
  } = getSemantics.getEvaluator

  def getEvaluator(ctx: Context)(using Provider): evaluators.DeterministicEvaluator {
    val program: self.type
  } = getSemantics.getEvaluator(using ctx)


  def transform(t: DefinitionTransformer { val s: self.trees.type }): Program { val trees: t.t.type } =
    Program(t.t)(symbols `transform` t)

  def transform(t: SymbolTransformer { val s: self.trees.type }): Program { val trees: t.t.type } =
    Program(t.t)(t `transform` symbols)

  def withFunctions(functions: Seq[trees.FunDef]): Program { val trees: self.trees.type } =
    Program(trees)(symbols `withFunctions` functions)

  def withSorts(sorts: Seq[trees.ADTSort]): Program { val trees: self.trees.type } =
    Program(trees)(symbols `withSorts` sorts)

  def asString(using Context): String = trees.asString(symbols)
  override def toString: String = asString(using Context.empty)
}

object Program {
  def apply(t: ast.Trees)(syms: t.Symbols): Program { val trees: t.type; val symbols: syms.type } = new Program {
    val trees: t.type = t
    val symbols: syms.type = syms
  }
}
