/* Copyright 2009-2016 EPFL, Lausanne */

package inox

trait Semantics { self =>
  val trees: ast.Trees
  val symbols: trees.Symbols
  val program: Program { val trees: self.trees.type; val symbols: self.symbols.type }

  private[this] val solverCache = new utils.LruCache[Options, solvers.SolverFactory {
    val program: self.program.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.program.type }
  }](5)

  private[this] val evaluatorCache = new utils.LruCache[Options, evaluators.DeterministicEvaluator {
    val program: self.program.type
  }](5)

  protected def createSolver(opts: Options): solvers.SolverFactory {
    val program: self.program.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.program.type }
  }

  protected def createEvaluator(opts: Options): evaluators.DeterministicEvaluator {
    val program: self.program.type
  }

  @inline
  def getSolver: solvers.SolverFactory {
    val program: self.program.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.program.type }
  } = getSolver(program.ctx.options)

  def getSolver(opts: Options): solvers.SolverFactory {
    val program: self.program.type
    type S <: solvers.combinators.TimeoutSolver { val program: self.program.type }
  } = solverCache.cached(opts, createSolver(opts))

  @inline
  def getEvaluator: evaluators.DeterministicEvaluator {
    val program: self.program.type
  } = getEvaluator(program.ctx.options)

  def getEvaluator(opts: Options): evaluators.DeterministicEvaluator {
    val program: self.program.type
  } = evaluatorCache.cached(opts, createEvaluator(opts))
}

trait SemanticsProvider { self =>
  val trees: ast.Trees
  def getSemantics(p: Program { val trees: self.trees.type }): p.Semantics
}
