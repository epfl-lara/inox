/* Copyright 2009-2016 EPFL, Lausanne */

import scala.language.implicitConversions

/** Core package of the Inox solving interface
  *
  * == Structure ==
  *
  * The package is organized in the following subpackages:
  *
  * [[inox.ast]]: Provides definitions for expressions, types and definitions,
  *   as well as operations on them
  * [[inox.evaluators]]: Evaluators of Inox expressions
  * [[inox.solvers]]: Interfaces to SMT-solvers
  * [[inox.tip]]: Parsing and printing for TIP problems
  * [[inox.transformers]]: Tree transformations for Inox expressions
  * [[inox.utils]]: Utility methods
  */
package object inox {
  implicit class BooleanToOption(cond: Boolean) {
    def option[A](v: => A) = if (cond) Some(v) else None
  }

  case class FatalError(msg: String) extends Exception(msg)

  /** We provide aliases to [[ast.Identifier]] and [[ast.FreshIdentifier]] here
    * for a more natural import experience.
    * 
    * Indeed, as Inox typically follows a pattern of nesting package clauses with
    * the outer-most being {{{package inox}}}, including these basic definitions
    * in the default imports makes my (@nv) life easier.
    */
  type Identifier = ast.Identifier

  /** @see [[Identifier]] for why this is here */
  val FreshIdentifier = ast.FreshIdentifier

  type InoxProgram = Program { val trees: inox.trees.type }

  object InoxProgram {
    def apply(ictx: Context,
      functions: Seq[inox.trees.FunDef],
      adts: Seq[inox.trees.ADTDefinition]): InoxProgram = new Program {
        val trees = inox.trees
        val ctx = ictx
        val symbols = new inox.trees.Symbols(
          functions.map(fd => fd.id -> fd).toMap,
          adts.map(cd => cd.id -> cd).toMap)
      }

    def apply(ictx: Context, sym: inox.trees.Symbols): InoxProgram = new Program {
      val trees = inox.trees
      val ctx = ictx
      val symbols = sym
    }
  }

  object trees extends ast.Trees with ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols

    object printer extends ast.Printer { val trees: inox.trees.type = inox.trees }
  }

  implicit lazy val inoxSemantics: SemanticsProvider { val trees: inox.trees.type } = new SemanticsProvider {
    val trees: inox.trees.type = inox.trees

    def getSemantics(p: Program { val trees: inox.trees.type }): p.Semantics = new inox.Semantics { self =>
      val trees: p.trees.type = p.trees
      val symbols: p.symbols.type = p.symbols

      // @nv: type system is unfortunately a little weak here...
      val program: Program { val trees: p.trees.type; val symbols: p.symbols.type } =
        p.asInstanceOf[Program { val trees: p.trees.type; val symbols: p.symbols.type }]

      protected def createSolver(opts: Options): solvers.SolverFactory {
        val program: self.program.type
        type S <: solvers.combinators.TimeoutSolver { val program: self.program.type }
      } = solvers.SolverFactory(self.program, opts)

      protected def createEvaluator(opts: Options): evaluators.DeterministicEvaluator {
        val program: self.program.type
      } = evaluators.RecursiveEvaluator(self.program, opts)
    }.asInstanceOf[p.Semantics]
  }
}
