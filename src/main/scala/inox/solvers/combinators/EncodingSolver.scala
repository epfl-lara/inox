/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

class EncodingSolver private(override val program: Program, override val context: inox.Context)
                            (protected val encoder: transformers.ProgramTransformer { val sourceProgram: program.type })
                            (protected val underlying: Solver {
                              val program: encoder.targetProgram.type
                            })
  extends Solver {
  import program.trees._
  import SolverResponses._

  def this(program: Program,
           encoder: transformers.ProgramTransformer { val sourceProgram: program.type },
           underlying: Solver { val program: encoder.targetProgram.type }) =
    this(program, underlying.context)(encoder)(underlying)

  protected val t: encoder.targetProgram.trees.type = encoder.targetProgram.trees

  val name = "E:" + underlying.name

  def declare(vd: ValDef) = underlying.declare(encoder.encode(vd))

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
