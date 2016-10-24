/* Copyright 2009-2016 EPFL, Lausanne */

/** Core package of the Inox solving interface
  *
  * == Structure ==
  *
  * The package is organized in the following subpackages:
  *
  * [[inox.ast]]: Provides definitions for expressions, types and definitions,
  *   as well as operations on them
  * [[inox.datagen]]: Generators/enumerators for Inox expressions
  * [[inox.evaluators]]: Evaluators of Inox expressions
  * [[inox.solvers]]: Interfaces to SMT-solvers
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
  }
}
