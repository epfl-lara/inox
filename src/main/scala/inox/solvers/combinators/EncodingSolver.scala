/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers
package combinators

trait EncodingSolver extends Solver {
  import program.trees._
  import SolverResponses._

  protected val encoder: ast.ProgramTransformer { val sourceProgram: program.type }
  protected lazy val t: encoder.targetProgram.trees.type = encoder.targetProgram.trees

  protected val underlying: Solver {
    val program: encoder.targetProgram.type
  }

  lazy val name = "E:" + underlying.name
  lazy val context = underlying.context

  def assertCnstr(expr: Expr) = underlying.assertCnstr(encoder.encode(expr))

  private def convert(config: Configuration)
                     (resp: config.Response[underlying.Model, underlying.Assumptions]):
                      config.Response[Model, Assumptions] = {
    config.convert(resp,
      (model: underlying.Model) => model.encode(encoder.reverse),
      (assumptions: underlying.Assumptions) => assumptions.map(encoder.decode)
    )
  }

  def check(config: CheckConfiguration) = convert(config)(underlying.check(config))
  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]) =
    convert(config)(underlying.checkAssumptions(config)(assumptions.map(encoder.encode)))

  def interrupt() = underlying.interrupt()
  def free() = underlying.free()
  def reset() = underlying.reset()
  def push() = underlying.push()
  def pop() = underlying.pop()
}
