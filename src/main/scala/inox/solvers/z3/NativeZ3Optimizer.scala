/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.z3

import com.microsoft.z3.Z3Exception

import z3.scala.{Z3Optimizer => ScalaZ3Optimizer, _}
import solvers._
import unrolling._

trait NativeZ3Optimizer extends AbstractUnrollingOptimizer with Z3Unrolling { self =>

  import program._
  import program.trees._
  import program.symbols._

  override val name = "native-z3-opt"

  protected object underlying extends {
    val program: targetProgram.type = targetProgram
    val options = self.options
  } with AbstractOptimizer with Z3Native {
    import program._
    import program.trees._
    import program.symbols._

    import SolverResponses._

    val name = "z3-opt"

    private[this] val optimizer: ScalaZ3Optimizer = z3.mkOptimizer()

    def assertCnstr(ast: Z3AST): Unit = optimizer.assertCnstr(ast)
    def assertCnstr(ast: Z3AST, weight: Int): Unit = optimizer.assertCnstr(ast, weight)
    def assertCnstr(ast: Z3AST, weight: Int, group: String): Unit = optimizer.assertCnstr(ast, weight, group)

    def check(config: CheckConfiguration) = config.cast(try {
      optimizer.check match {
        case Some(true) => if (config.withModel) SatWithModel(optimizer.getModel) else Sat
        case Some(false) => Unsat
        case None => Unknown
      }
    } catch {
      // @nv: Z3 optimizer throws an exceptiopn when canceled instead of returning None
      case e: Z3Exception if e.getMessage == "canceled" => Unknown
    })

    def checkAssumptions(config: Configuration)(assumptions: Set[Z3AST]) = {
      optimizer.push()
      for (a <- assumptions) optimizer.assertCnstr(a)
      val res: config.Response[Model, Assumptions] = config.cast(try {
        optimizer.check match {
          case Some(true) => if (config.withModel) SatWithModel(optimizer.getModel) else Sat
          case Some(false) => if (config.withUnsatAssumptions) UnsatWithAssumptions(Set()) else Unsat
          case None => Unknown
        }
      } catch {
        // @nv: Z3 optimizer throws an exceptiopn when canceled instead of returning None
        case e: Z3Exception if e.getMessage == "canceled" => Unknown
      })
      optimizer.pop()
      res
    }

    lazy val semantics = targetSemantics

    override def push(): Unit = {
      super.push()
      optimizer.push()
    }

    override def pop(): Unit = {
      super.pop()
      optimizer.pop()
    }
  }
}
