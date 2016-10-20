/* Copyright 2009-2016 EPFL, Lausanne */

package inox
package solvers.z3

import solvers.{z3 => _, _}
import unrolling._
import theories._

import z3.scala._

trait NativeZ3Solver extends AbstractUnrollingSolver { self =>

  import program._
  import program.trees._
  import program.symbols._

  override val name = "NativeZ3"

  type Encoded = Z3AST

  object theories extends {
    val sourceProgram: self.encoder.targetProgram.type = self.encoder.targetProgram
  } with StringEncoder

  protected object underlying extends {
    val program: targetProgram.type = targetProgram
    val options = self.options
  } with AbstractZ3Solver

  private lazy val z3 = underlying.z3

  object templates extends {
    val program: targetProgram.type = targetProgram
  } with Templates {
    import program.trees._

    type Encoded = self.Encoded

    def asString(ast: Z3AST): String = ast.toString

    def encodeSymbol(v: Variable): Z3AST = underlying.symbolToFreshZ3Symbol(v)

    def mkEncoder(bindings: Map[Variable, Z3AST])(e: Expr): Z3AST = {
      underlying.toZ3Formula(e, bindings)
    }

    def mkSubstituter(substMap: Map[Z3AST, Z3AST]): Z3AST => Z3AST = {
      val (from, to) = substMap.unzip
      val (fromArray, toArray) = (from.toArray, to.toArray)

      (c: Z3AST) => z3.substitute(c, fromArray, toArray)
    }

    def mkNot(e: Z3AST) = z3.mkNot(e)
    def mkOr(es: Z3AST*) = z3.mkOr(es : _*)
    def mkAnd(es: Z3AST*) = z3.mkAnd(es : _*)
    def mkEquals(l: Z3AST, r: Z3AST) = z3.mkEq(l, r)
    def mkImplies(l: Z3AST, r: Z3AST) = z3.mkImplies(l, r)
  }

  override def reset(): Unit = {
    super.reset()
    underlying.reset()
  }

  def free(): Unit = underlying.free()

  protected def declareVariable(v: t.Variable): Z3AST = underlying.declareVariable(v)

  protected def wrapModel(model: Z3Model): super.ModelWrapper = ModelWrapper(model)

  private case class ModelWrapper(model: Z3Model) extends super.ModelWrapper {
    def modelEval(elem: Z3AST, tpe: t.Type): Option[t.Expr] = {
      val timer = ctx.timers.solvers.z3.eval.start()
      val res = tpe match {
        case t.BooleanType => model.evalAs[Boolean](elem).map(t.BooleanLiteral)
        case t.Int32Type => model.evalAs[Int](elem).map(t.IntLiteral(_)).orElse {
          model.eval(elem).flatMap(term => underlying.softFromZ3Formula(model, term, t.Int32Type))
        }
        case t.IntegerType => model.evalAs[Int](elem).map(t.IntegerLiteral(_))
        case other => model.eval(elem) match {
          case None => None
          case Some(t) => underlying.softFromZ3Formula(model, t, other)
        }
      }
      timer.stop()
      res
    }

    override def toString = model.toString
  }

  override def push(): Unit = {
    super.push()
    underlying.push()
  }

  override def pop(): Unit = {
    super.pop()
    underlying.pop()
  }

  override def interrupt(): Unit = {
    underlying.interrupt()
    super.interrupt()
  }
}
