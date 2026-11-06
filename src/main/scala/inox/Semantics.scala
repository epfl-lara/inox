/* Copyright 2009-2018 EPFL, Lausanne */

package inox

trait Semantics { self =>
  val trees: ast.Trees
  val symbols: trees.Symbols
  val program: Program { val trees: self.trees.type; val symbols: self.symbols.type }

  private val solverCache = new utils.LruCache[Context, solvers.SolverFactory {
    val program: self.program.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.program.type }
  }](5)

  private val evaluatorCache = new utils.LruCache[Context, evaluators.DeterministicEvaluator {
    val program: self.program.type
  }](5)

  protected def createSolver(ctx: Context): solvers.SolverFactory {
    val program: self.program.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.program.type }
  }

  protected def createEvaluator(ctx: Context): evaluators.DeterministicEvaluator {
    val program: self.program.type
  }

  def getSolver(using ctx: Context): solvers.SolverFactory {
    val program: self.program.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.program.type }
  } = solverCache.cached(ctx, createSolver(ctx))

  def getEvaluator(using ctx: Context): evaluators.DeterministicEvaluator {
    val program: self.program.type
  } = evaluatorCache.cached(ctx, createEvaluator(ctx))

  /** The semantics of the program extended with `functions`, under which the values of a model
    * that defines functions are typed and evaluated (see [[Model.symbols]]).
    *
    * Semantics that support such models override this, typically by building the extended
    * program's semantics with the provider that created them.
    */
  def withFunctions(functions: Seq[trees.FunDef]): inox.Semantics { val trees: self.trees.type } =
    if (functions.isEmpty) this
    else throw FatalError("These semantics do not support programs extended with new functions")
}

trait SemanticsProvider { self =>
  val trees: ast.Trees
  def getSemantics(p: Program { val trees: self.trees.type }): p.Semantics
}
