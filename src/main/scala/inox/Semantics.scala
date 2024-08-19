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
}

trait SemanticsProvider { self =>
  val trees: ast.Trees
  def getSemantics(p: Program { val trees: self.trees.type }): p.Semantics
}
